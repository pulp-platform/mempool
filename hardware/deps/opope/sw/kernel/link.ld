/* Copyright 2025 ETH Zurich and University of Bologna. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Danilo Cammarata <dcammarata@iis.ee.ethz.ch> */

SEARCH_DIR(.)
__DYNAMIC  =  0;

MEMORY
{
    instrram    : ORIGIN = 0x1c000000, LENGTH = 0x8000
    dataram     : ORIGIN = 0x1c010000, LENGTH = 0xb0000 
    stack       : ORIGIN = 0x1c0c0000, LENGTH = 0xb0000
}

/* Stack information variables */
_min_stack      = 0x1000;   /* 4K - minimum stack space to reserve */
_stack_len     = LENGTH(stack);
_stack_start   = ORIGIN(stack) + LENGTH(stack);

/* We have to align each sector to word boundaries as our current s19->slm
 * conversion scripts are not able to handle non-word aligned sections. */

SECTIONS
{
    .vectors :
    {
        . = ALIGN(4);
        KEEP(*(.vectors))
    } > instrram

    .text : {
        . = ALIGN(4);
        _stext = .;
        *(.text)
        _etext  =  .;
        __CTOR_LIST__ = .;
        LONG((__CTOR_END__ - __CTOR_LIST__) / 4 - 2)
        *(.ctors)
        LONG(0)
        __CTOR_END__ = .;
        __DTOR_LIST__ = .;
        LONG((__DTOR_END__ - __DTOR_LIST__) / 4 - 2)
        *(.dtors)
        LONG(0)
        __DTOR_END__ = .;
        *(.lit)
        *(.shdata)
        _endtext = .;
    }  > instrram

    /*--------------------------------------------------------------------*/
    /* Global constructor/destructor segment                              */
    /*--------------------------------------------------------------------*/

    .preinit_array     :
    {
      PROVIDE_HIDDEN (__preinit_array_start = .);
      KEEP (*(.preinit_array))
      PROVIDE_HIDDEN (__preinit_array_end = .);
    } > dataram

    .init_array     :
    {
      PROVIDE_HIDDEN (__init_array_start = .);
      KEEP (*(SORT(.init_array.*)))
      KEEP (*(.init_array ))
      PROVIDE_HIDDEN (__init_array_end = .);
    } > dataram

    .fini_array     :
    {
      PROVIDE_HIDDEN (__fini_array_start = .);
      KEEP (*(SORT(.fini_array.*)))
      KEEP (*(.fini_array ))
      PROVIDE_HIDDEN (__fini_array_end = .);
    } > dataram

  

    .rodata : {
        . = ALIGN(4);
        *(.rodata);
        *(.rodata.*)
    } > dataram

    .shbss :
    {
        . = ALIGN(4);
        *(.shbss)
    } > dataram

	  .golden_output 0x1c020000 :
	  {
	      __golden_output_start = .;
	      KEEP(*(.golden_output))
	      __golden_output_end = .;
	  } > dataram

	  .x_buffer 0x1c040000 :
	  {
	      __x_buffer_start = .;
	      KEEP(*(.x_buffer))
	      __x_buffer_end = .;
	  } > dataram

	  .w_buffer 0x1c060000 :
	  {
	      __w_buffer_start = .;
	      KEEP(*(.w_buffer))
	      __w_buffer_end = .;
	  } > dataram

	  .y_buffer 0x1c080000 :
	  {
	      __y_buffer_start = .;
	      KEEP(*(.y_buffer))
	      __y_buffer_end = .;
	  } > dataram

    .data : {
        . = ALIGN(4);
        sdata  =  .;
        _sdata  =  .;
        *(.data);
        *(.data.*)
        edata  =  .;
        _edata  =  .;
    } > dataram

    .bss :
    {
        . = ALIGN(4);
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
        *(COMMON)
        _bss_end = .;
    } > dataram

    /* ensure there is enough room for stack */
    .stack (NOLOAD): {
        . = ALIGN(4);
        . = . + _min_stack ;
        . = ALIGN(4);
        stack = . ;
        _stack = . ;
    } > stack

}

