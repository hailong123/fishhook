// Copyright (c) 2013, Facebook, Inc.
// All rights reserved.
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//   * Redistributions of source code must retain the above copyright notice,
//     this list of conditions and the following disclaimer.
//   * Redistributions in binary form must reproduce the above copyright notice,
//     this list of conditions and the following disclaimer in the documentation
//     and/or other materials provided with the distribution.
//   * Neither the name Facebook nor the names of its contributors may be used to
//     endorse or promote products derived from this software without specific
//     prior written permission.
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "fishhook.h"

#include <dlfcn.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <mach/mach.h>
#include <mach/vm_map.h>
#include <mach/vm_region.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>

#ifdef __LP64__
typedef struct mach_header_64 mach_header_t;
typedef struct segment_command_64 segment_command_t;
typedef struct section_64 section_t;
typedef struct nlist_64 nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT_64
#else
typedef struct mach_header mach_header_t;
typedef struct segment_command segment_command_t;
typedef struct section section_t;
typedef struct nlist nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT
#endif

#ifndef SEG_DATA_CONST
#define SEG_DATA_CONST  "__DATA_CONST"
#endif

struct rebinding {
  const char *name;// 函数名称
  void *replacement;// 新的函数指针
  void **replaced;// 保存原始函数地址的变量的指针
};


struct rebindings_entry {
  struct rebinding *rebindings; //重新绑定的 rebindings 结构体
  size_t rebindings_nel; //重新绑定的函数数量
  struct rebindings_entry *next; //链表的下一个节点
};

static struct rebindings_entry *_rebindings_head;

static int prepend_rebindings(struct rebindings_entry **rebindings_head,
                              struct rebinding rebindings[],
                              size_t nel) {

  //申请一个 rebindings_entry 结构体的内存空间
  struct rebindings_entry *new_entry = (struct rebindings_entry *) malloc(sizeof(struct rebindings_entry));
  if (!new_entry) {
    return -1;
  }


  //申请 nel 个 rebinding 结构体的内存空间
  new_entry->rebindings = (struct rebinding *) malloc(sizeof(struct rebinding) * nel);
  if (!new_entry->rebindings) {
    free(new_entry);
    return -1;
  }


  //将 rebindings 的值 拷贝到 new_entry->rebindings
  memcpy(new_entry->rebindings, rebindings, sizeof(struct rebinding) * nel);

  //赋值操作
  new_entry->rebindings_nel = nel;

  //新节点插入到头节点
  new_entry->next = *rebindings_head;
  
  *rebindings_head = new_entry;
  
  return 0;
}


static vm_prot_t get_protection(void *sectionStart) {
  mach_port_t task = mach_task_self();
  vm_size_t size = 0;
  vm_address_t address = (vm_address_t)sectionStart;
  memory_object_name_t object;
#if __LP64__
  mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT_64;
  vm_region_basic_info_data_64_t info;
  kern_return_t info_ret = vm_region_64(
      task, &address, &size, VM_REGION_BASIC_INFO_64, (vm_region_info_64_t)&info, &count, &object);
#else
  mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT;
  vm_region_basic_info_data_t info;
  kern_return_t info_ret = vm_region(task, &address, &size, VM_REGION_BASIC_INFO, (vm_region_info_t)&info, &count, &object);
#endif
  if (info_ret == KERN_SUCCESS) {
    return info.protection;
  } else {
    return VM_PROT_READ;
  }
}

//定位 __nl_symbol_ptr 和 __la_symbol_ptr 以及对其中的具体函数进行重绑定工作
static void perform_rebinding_with_section(struct rebindings_entry *rebindings,
                                           section_t *section,
                                           intptr_t slide,
                                           nlist_t *symtab,
                                           char *strtab,
                                           uint32_t *indirect_symtab) {

  const bool isDataConst = strcmp(section->segname, SEG_DATA_CONST) == 0;
  //还记得 reserved1 么, nl_symbol_ptr 和 la_symbol_ptrsection中的reserved1 表示在动态符号表中的起始Index
  uint32_t *indirect_symbol_indices = indirect_symtab + section->reserved1;
  //找到 __nl_symbol_ptr 和 __la_symbol_ptr 里面函数指针存放的地方
  void **indirect_symbol_bindings = (void **)((uintptr_t)slide + section->addr);
  vm_prot_t oldProtection = VM_PROT_READ;
  if (isDataConst) {
    oldProtection = get_protection(rebindings);
    //mprotect 修改指定内容的 权限
    mprotect(indirect_symbol_bindings, section->size, PROT_READ | PROT_WRITE);
  }

  //遍历 section 中的符号
  for (uint i = 0; i < section->size / sizeof(void *); i++) {
    //找到该符号在动态符号表中的位置
    uint32_t symtab_index = indirect_symbol_indices[i];
    if (symtab_index == INDIRECT_SYMBOL_ABS || symtab_index == INDIRECT_SYMBOL_LOCAL ||
        symtab_index == (INDIRECT_SYMBOL_LOCAL   | INDIRECT_SYMBOL_ABS)) {
      continue;
    }
    /*
    This is the symbol table entry structure for 32-bit architectures.
    struct nlist {
      union {
          uint32_t n_strx;    /* index into the string table */
      } n_un;
  
      uint8_t n_type;        /* type flag, see below */
      uint8_t n_sect;        /* section number or NO_SECT */
      int16_t n_desc;        /* see <mach-o/stab.h> */
      uint32_t n_value;    /* value of this symbol (or stab offset) */
   };
*/
    //symtab[symtab_index] 对应符号表中的符号
    //找到符号在符号表中的偏移
    uint32_t strtab_offset = symtab[symtab_index].n_un.n_strx;
    //找到符号的名字
    char *symbol_name = strtab + strtab_offset;
    //判断符号大于两个字符, 为什么是两个? 因为符号前带有 "_" 下划线
    bool symbol_name_longer_than_1 = symbol_name[0] && symbol_name[1];
    //fishhook 内部做了单向链表来存储所有的钩子结构体
    struct rebindings_entry *cur = rebindings;
    while (cur) {
      //遍历所有的节点
      for (uint j = 0; j < cur->rebindings_nel; j++) {
        //判断符号表中取出来的和外部传入要hook的符号名称是否一致
        if (symbol_name_longer_than_1 &&
            strcmp(&symbol_name[1], cur->rebindings[j].name) == 0) {
          if (cur->rebindings[j].replaced != NULL &&
              indirect_symbol_bindings[i] != cur->rebindings[j].replacement) {
            //indirect_symbol_bindings[i]: __nl_symbol_ptr 和 __la_symbol_ptr 里面的函数指针之一
            //用 cur->rebindings[j].replaced 保存原指针指向
            *(cur->rebindings[j].replaced) = indirect_symbol_bindings[i];
          }
          //将原函数指针替换为 cur->rebindings[j].replacement 这样调用原函数就变成了调用我们指定的替换函数
          indirect_symbol_bindings[i] = cur->rebindings[j].replacement;
          goto symbol_loop;
        }
      }
      cur = cur->next;
    }
  symbol_loop:;
  }
  if (isDataConst) {
    int protection = 0;
    if (oldProtection & VM_PROT_READ) {
      protection |= PROT_READ;
    }
    if (oldProtection & VM_PROT_WRITE) {
      protection |= PROT_WRITE;
    }
    if (oldProtection & VM_PROT_EXECUTE) {
      protection |= PROT_EXEC;
    }
    mprotect(indirect_symbol_bindings, section->size, protection);
  }
}


//定位 Mach-O 中 __nl_symbol_ptr 和 __la_symbol_ptr 所在 section 以及 符号表, 动态符号表, 字符串表的过程
static void rebind_symbols_for_image(struct rebindings_entry *rebindings,
                                     const struct mach_header *header,
                                     intptr_t slide) {
  Dl_info info;
  //获取 header 所在的模块, 地址
  if (dladdr(header, &info) == 0) {
    return;
  }

  segment_command_t *cur_seg_cmd;
  segment_command_t *linkedit_segment = NULL;
  struct symtab_command* symtab_cmd = NULL;
  struct dysymtab_command* dysymtab_cmd = NULL;


//header 的偏移 +header 的大小, 目的是跳过 Mach-O 中的header部分寻找 Segment
  uintptr_t cur = (uintptr_t)header + sizeof(mach_header_t);
  //header->ncmds 加载命令数量
  for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
    //当前的 Load Command
    cur_seg_cmd = (segment_command_t *)cur;
    //类型是 LC_SEGMENT
    if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {
      //找到 __LINKEDIT 段
      //为什么要寻找__LINKDIT? fishhook 通过 __LINKDIT 的内存地址中的偏移 - __LINKEDIT 在文件中的偏移 + slide = 文件加载的基地址
      //那么slide是什么? 因为 ASLR 的缘故, Mach-O 文件加载的时候地址随机, Mach-O 文件每次加载进内存的时候地址都是不一样的. 这个Slide就是本次加载到内存上的偏移
      if (strcmp(cur_seg_cmd->segname, SEG_LINKEDIT) == 0) {
        linkedit_segment = cur_seg_cmd;
      }
    } else if (cur_seg_cmd->cmd == LC_SYMTAB) {
      //找到符号表
      symtab_cmd = (struct symtab_command*)cur_seg_cmd;
    } else if (cur_seg_cmd->cmd == LC_DYSYMTAB) {
      //找到动态符号表
      dysymtab_cmd = (struct dysymtab_command*)cur_seg_cmd;
    }
  }

//容错处理
  if (!symtab_cmd || !dysymtab_cmd || !linkedit_segment ||
      !dysymtab_cmd->nindirectsyms) {
    return;
  }

  // Find base symbol/string table addresses
  //linkedit_base 即面前提到的基地 = ASLR(随机地址偏移) + 虚拟内存的地址 - 在文件中的偏移地址
  uintptr_t linkedit_base = (uintptr_t)slide + linkedit_segment->vmaddr - linkedit_segment->fileoff;
  //找到符号表
  nlist_t *symtab = (nlist_t *)(linkedit_base + symtab_cmd->symoff);
   //还记得符号表的结构吗？
  /*
  struct symtab_command {
  uint32_t  cmd;    // LC_SYMTAB
  uint32_t  cmdsize;  // sizeof(struct symtab_command)
  uint32_t  symoff;   // symbol table offset 
  uint32_t  nsyms;    // number of symbol table entries
  uint32_t  stroff;   // string table offset
  uint32_t  strsize;  // string table size in bytes
  };
  */
  //stroff : 字符串表的偏移
  //找到字符串表
  char *strtab = (char *)(linkedit_base + symtab_cmd->stroff);

  //找到动态符号表
  // Get indirect symbol table (array of uint32_t indices into symbol table)
  uint32_t *indirect_symtab = (uint32_t *)(linkedit_base + dysymtab_cmd->indirectsymoff);

  cur = (uintptr_t)header + sizeof(mach_header_t);

  //再次遍历 Load Commands
  for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
    cur_seg_cmd = (segment_command_t *)cur;
    if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {
      //寻找__DATA 和 __DATA_CONST的section
      if (strcmp(cur_seg_cmd->segname, SEG_DATA) != 0 &&
          strcmp(cur_seg_cmd->segname, SEG_DATA_CONST) != 0) {
        continue;
      }

      //cur_seg_cmd->nsects: segment 中section的数量
      //遍历所有的section
      for (uint j = 0; j < cur_seg_cmd->nsects; j++) {
        section_t *sect =
          (section_t *)(cur + sizeof(segment_command_t)) + j;
          //找到 __la_symbol_ptr 需要延迟绑定的符号
        if ((sect->flags & SECTION_TYPE) == S_LAZY_SYMBOL_POINTERS) {
          perform_rebinding_with_section(rebindings, sect, slide, symtab, strtab, indirect_symtab);
        }
        //寻找 __nl_symbol_ptr 非延迟绑定的符号
        if ((sect->flags & SECTION_TYPE) == S_NON_LAZY_SYMBOL_POINTERS) {
          perform_rebinding_with_section(rebindings, sect, slide, symtab, strtab, indirect_symtab);
        }
      }
    }
  }
}

//什么都没做,直接透传给  rebind_symbols_for_image 
static void _rebind_symbols_for_image(const struct mach_header *header,
                                      intptr_t slide) {
    rebind_symbols_for_image(_rebindings_head, header, slide);
}


//绑定符号表镜像
int rebind_symbols_image(void *header,
                         intptr_t slide,
                         struct rebinding rebindings[],
                         size_t rebindings_nel) {
    
    struct rebindings_entry *rebindings_head = NULL;
    
    int retval = prepend_rebindings(&rebindings_head, rebindings, rebindings_nel);
    
    rebind_symbols_for_image(rebindings_head, (const struct mach_header *) header, slide);

    if (rebindings_head) {
      free(rebindings_head->rebindings);
    }

    free(rebindings_head);
    
    return retval;
}


//绑定符号表
int rebind_symbols(struct rebinding rebindings[], size_t rebindings_nel) {
  //将 rebindings 数组插入到链表结构体中的头节点
  int retval = prepend_rebindings(&_rebindings_head, rebindings, rebindings_nel);
  if (retval < 0) {
    return retval;
  }

  //头节点没有下一个节点那说明当前链表只有刚插入的节点, 这说明是第一次调用
  // If this was the first call, register callback for image additions (which is also invoked for
  // existing images, otherwise, just run on existing images
  if (!_rebindings_head->next) {
    _dyld_register_func_for_add_image(_rebind_symbols_for_image); //动态库被加载会调用这个函数, 同时已经加载的库也会回调
  } else {
    //直接遍历所有的动态库进行重绑定
    uint32_t c = _dyld_image_count();
    for (uint32_t i = 0; i < c; i++) {
      _rebind_symbols_for_image(_dyld_get_image_header(i), _dyld_get_image_vmaddr_slide(i));
    }
  }
  return retval;
}
