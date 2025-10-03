/*

Copyright (c) 2004,2012 Kustaa Nyholm / SpareTimeLabs

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of Kustaa Nyholm or SpareTimeLabs nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDER BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

This modified tinyprintf is distributed under the conditions of the BSD-new license
as explicitly allowed:
 -> https://github.com/cjlano/tinyprintf commit 2ee3012

They provide a simple and small (+400 loc) printf functionality to
be used in embedded systems.

I've found them so useful in debugging that I do not bother with a
debugger at all.

They are distributed in source form, so to use them, just compile them
into your project.

Two printf variants are provided: printf and the 'sprintf' family of
functions ('snprintf', 'sprintf', 'vsnprintf', 'vsprintf').

The formats supported by this implementation are:
'c' 'd' 'i' 'o' 'p' 'u' 's' 'x' 'X'.

Zero padding and field width are also supported.

If the library is compiled with 'PRINTF_SUPPORT_LONG' defined, then
the long specifier is also supported. Note that this will pull in some
long math routines (pun intended!) and thus make your executable
noticeably longer. Likewise with 'PRINTF_LONG_LONG_SUPPORT' for the
long long specifier, and with 'PRINTF_SIZE_T_SUPPORT' for the size_t
specifier.

The memory footprint of course depends on the target CPU, compiler and
compiler options, but a rough guesstimate (based on a H8S target) is about
1.4 kB for code and some twenty 'int's and 'char's, say 60 bytes of stack space.
Not too bad. Your mileage may vary. By hacking the source code you can
get rid of some hundred bytes, I'm sure, but personally I feel the balance of
functionality and flexibility versus  code size is close to optimal for
many embedded systems.

To use the printf, you need to supply your own character output function,
something like :

void putc ( void* p, char c)
{
    while (!SERIAL_PORT_EMPTY) ;
    SERIAL_PORT_TX_REGISTER = c;
}

Before you can call printf, you need to initialize it to use your
character output function with something like:

init_printf(NULL,putc);

Notice the 'NULL' in 'init_printf' and the parameter 'void* p' in 'putc',
the NULL (or any pointer) you pass into the 'init_printf' will eventually be
passed to your 'putc' routine. This allows you to pass some storage space (or
anything really) to the character output function, if necessary.
This is not often needed but it was implemented like that because it made
implementing the sprintf function so neat (look at the source code).

The code is re-entrant, except for the 'init_printf' function, so it is safe
to call it from interrupts too, although this may result in mixed output.
If you rely on re-entrancy, take care that your 'putc' function is re-entrant!

The printf and sprintf functions are actually macros that translate to
'tfp_printf' and 'tfp_sprintf' when 'TINYPRINTF_OVERRIDE_LIBC' is set
(default). Setting it to 0 makes it possible to use them along with
'stdio.h' printf's in a single source file. When
'TINYPRINTF_OVERRIDE_LIBC' is set, please note that printf/sprintf are
not function-like macros, so if you have variables or struct members
with these names, things will explode in your face.  Without variadic
macros this is the best we can do to wrap these function. If it is a
problem, just give up the macros and use the functions directly, or
rename them.

It is also possible to avoid defining tfp_printf and/or tfp_sprintf by
clearing 'TINYPRINTF_DEFINE_TFP_PRINTF' and/or
'TINYPRINTF_DEFINE_TFP_SPRINTF' to 0. This allows for example to
export only tfp_format, which is at the core of all the other
functions.

For further details see source code.

regs Kusti, 23.10.2004
*/

void putf(char *null, char c) {
  *(volatile int *) (0x80000004) = (int)c;
}

#ifndef __TFP_PRINTF__
#define __TFP_PRINTF__

#include <stdarg.h>

/* Global configuration */

/* Set this to 0 if you do not want to provide tfp_printf */
#ifndef TINYPRINTF_DEFINE_TFP_PRINTF
# define TINYPRINTF_DEFINE_TFP_PRINTF 1
#endif

/* Set this to 0 if you do not want to provide
   tfp_sprintf/snprintf/vsprintf/vsnprintf */
#ifndef TINYPRINTF_DEFINE_TFP_SPRINTF
# define TINYPRINTF_DEFINE_TFP_SPRINTF 1
#endif

/* Set this to 0 if you do not want tfp_printf and
   tfp_{vsn,sn,vs,s}printf to be also available as
   printf/{vsn,sn,vs,s}printf */
#ifndef TINYPRINTF_OVERRIDE_LIBC
# define TINYPRINTF_OVERRIDE_LIBC 1
#endif

/* Optional external types dependencies */

#if TINYPRINTF_DEFINE_TFP_SPRINTF
# include <sys/types.h>  /* size_t */
#endif

/* Declarations */

#ifdef __GNUC__
# define _TFP_SPECIFY_PRINTF_FMT(fmt_idx,arg1_idx) \
    __attribute__((format (printf, fmt_idx, arg1_idx)))
#else
# define _TFP_SPECIFY_PRINTF_FMT(fmt_idx,arg1_idx)
#endif

#ifdef  __cplusplus
extern "C" {
#endif

typedef void (*putcf) (void *, char);

/*
   'tfp_format' really is the central function for all tinyprintf. For
   each output character after formatting, the 'putf' callback is
   called with 2 args:
     - an arbitrary void* 'putp' param defined by the user and
       passed unmodified from 'tfp_format',
     - the character.
   The 'tfp_printf' and 'tfp_sprintf' functions simply define their own
   callback and pass to it the right 'putp' it is expecting.
*/
void tfp_format(void *putp, putcf putf, const char *fmt, va_list va);

#if TINYPRINTF_DEFINE_TFP_SPRINTF
int tfp_vsnprintf(char *str, size_t size, const char *fmt, va_list ap);
int tfp_snprintf(char *str, size_t size, const char *fmt, ...) \
     _TFP_SPECIFY_PRINTF_FMT(3, 4);
int tfp_vsprintf(char *str, const char *fmt, va_list ap);
int tfp_sprintf(char *str, const char *fmt, ...) \
    _TFP_SPECIFY_PRINTF_FMT(2, 3);
# if TINYPRINTF_OVERRIDE_LIBC
#  define vsnprintf tfp_vsnprintf
#  define snprintf tfp_snprintf
#  define vsprintf tfp_vsprintf
#  define sprintf tfp_sprintf
# endif
#endif

#if TINYPRINTF_DEFINE_TFP_PRINTF
void init_printf(void *putp, putcf putf);
void tfp_printf(char *fmt, ...) _TFP_SPECIFY_PRINTF_FMT(1, 2);
# if TINYPRINTF_OVERRIDE_LIBC
#  define printf tfp_printf
# endif
#endif

#ifdef  __cplusplus
}
#endif

#endif



/*
 * Configuration
 */

/* Enable long int support */
// #define PRINTF_LONG_SUPPORT

/* Enable long long int support (implies long int support) */
// #define PRINTF_LONG_LONG_SUPPORT

/* Enable %z (size_t) support */
// #define PRINTF_SIZE_T_SUPPORT

/*
 * Configuration adjustments
 */
#ifdef PRINTF_SIZE_T_SUPPORT
#include <sys/types.h>
#endif

#ifdef PRINTF_LONG_LONG_SUPPORT
# define PRINTF_LONG_SUPPORT
#endif

/* __SIZEOF_<type>__ defined at least by gcc */
#ifdef __SIZEOF_POINTER__
# define SIZEOF_POINTER __SIZEOF_POINTER__
#endif
#ifdef __SIZEOF_LONG_LONG__
# define SIZEOF_LONG_LONG __SIZEOF_LONG_LONG__
#endif
#ifdef __SIZEOF_LONG__
# define SIZEOF_LONG __SIZEOF_LONG__
#endif
#ifdef __SIZEOF_INT__
# define SIZEOF_INT __SIZEOF_INT__
#endif

#ifdef __GNUC__
# define _TFP_GCC_NO_INLINE_  __attribute__ ((noinline))
#else
# define _TFP_GCC_NO_INLINE_
#endif

/*
 * Implementation
 */
struct param {
    char lz:1;          /**<  Leading zeros */
    char alt:1;         /**<  alternate form */
    char uc:1;          /**<  Upper case (for base16 only) */
    char align_left:1;  /**<  0 == align right (default), 1 == align left */
    unsigned int width; /**<  field width */
    char sign;          /**<  The sign to display (if any) */
    unsigned int base;  /**<  number base (e.g.: 8, 10, 16) */
    char *bf;           /**<  Buffer to output */
};


#ifdef PRINTF_LONG_LONG_SUPPORT
static void _TFP_GCC_NO_INLINE_ ulli2a(
    unsigned long long int num, struct param *p)
{
    int n = 0;
    unsigned long long int d = 1;
    char *bf = p->bf;
    while (num / d >= p->base)
        d *= p->base;
    while (d != 0) {
        int dgt = num / d;
        num %= d;
        d /= p->base;
        if (n || dgt > 0 || d == 0) {
            *bf++ = dgt + (dgt < 10 ? '0' : (p->uc ? 'A' : 'a') - 10);
            ++n;
        }
    }
    *bf = 0;
}

static void lli2a(long long int num, struct param *p)
{
    if (num < 0) {
        num = -num;
        p->sign = '-';
    }
    ulli2a(num, p);
}
#endif

#ifdef PRINTF_LONG_SUPPORT
static void uli2a(unsigned long int num, struct param *p)
{
    int n = 0;
    unsigned long int d = 1;
    char *bf = p->bf;
    while (num / d >= p->base)
        d *= p->base;
    while (d != 0) {
        int dgt = num / d;
        num %= d;
        d /= p->base;
        if (n || dgt > 0 || d == 0) {
            *bf++ = dgt + (dgt < 10 ? '0' : (p->uc ? 'A' : 'a') - 10);
            ++n;
        }
    }
    *bf = 0;
}

static void li2a(long num, struct param *p)
{
    if (num < 0) {
        num = -num;
        p->sign = '-';
    }
    uli2a(num, p);
}
#endif

static void ui2a(unsigned int num, struct param *p)
{
    int n = 0;
    unsigned int d = 1;
    char *bf = p->bf;
    while (num / d >= p->base)
        d *= p->base;
    while (d != 0) {
        int dgt = num / d;
        num %= d;
        d /= p->base;
        if (n || dgt > 0 || d == 0) {
            *bf++ = dgt + (dgt < 10 ? '0' : (p->uc ? 'A' : 'a') - 10);
            ++n;
        }
    }
    *bf = 0;
}

static void i2a(int num, struct param *p)
{
    if (num < 0) {
        num = -num;
        p->sign = '-';
    }
    ui2a(num, p);
}

static int a2d(char ch)
{
    if (ch >= '0' && ch <= '9')
        return ch - '0';
    else if (ch >= 'a' && ch <= 'f')
        return ch - 'a' + 10;
    else if (ch >= 'A' && ch <= 'F')
        return ch - 'A' + 10;
    else
        return -1;
}

static char a2u(char ch, const char **src, int base, unsigned int *nump)
{
    const char *p = *src;
    unsigned int num = 0;
    int digit;
    while ((digit = a2d(ch)) >= 0) {
        if (digit > base)
            break;
        num = num * base + digit;
        ch = *p++;
    }
    *src = p;
    *nump = num;
    return ch;
}

static void putchw(void *putp, putcf putf__, struct param *p)
{
    char ch;
    int n = p->width;
    char *bf = p->bf;

    /* Number of filling characters */
    while (*bf++ && n > 0)
        n--;
    if (p->sign)
        n--;
    if (p->alt && p->base == 16)
        n -= 2;
    else if (p->alt && p->base == 8)
        n--;

    /* Fill with space to align to the right, before alternate or sign */
    if (!p->lz && !p->align_left) {
        while (n-- > 0)
            putf(putp, ' ');
    }

    /* print sign */
    if (p->sign)
        putf(putp, p->sign);

    /* Alternate */
    if (p->alt && p->base == 16) {
        putf(putp, '0');
        putf(putp, (p->uc ? 'X' : 'x'));
    } else if (p->alt && p->base == 8) {
        putf(putp, '0');
    }

    /* Fill with zeros, after alternate or sign */
    if (p->lz) {
        while (n-- > 0)
            putf(putp, '0');
    }

    /* Put actual buffer */
    bf = p->bf;
    while ((ch = *bf++))
        putf(putp, ch);

    /* Fill with space to align to the left, after string */
    if (!p->lz && p->align_left) {
        while (n-- > 0)
            putf(putp, ' ');
    }
}

void tfp_format(void *putp, putcf putf__, const char *fmt, va_list va)
{
    struct param p;
#ifdef PRINTF_LONG_SUPPORT
    char bf[23];  /* long = 64b on some architectures */
#else
    char bf[12];  /* int = 32b on some architectures */
#endif
    char ch;
    p.bf = bf;

    while ((ch = *(fmt++))) {
        if (ch != '%') {
            putf(putp, ch);
        } else {
#ifdef PRINTF_LONG_SUPPORT
            char lng = 0;  /* 1 for long, 2 for long long */
#endif
            /* Init parameter struct */
            p.lz = 0;
            p.alt = 0;
            p.width = 0;
            p.align_left = 0;
            p.sign = 0;

            /* Flags */
            while ((ch = *(fmt++))) {
                switch (ch) {
                case '-':
                    p.align_left = 1;
                    continue;
                case '0':
                    p.lz = 1;
                    continue;
                case '#':
                    p.alt = 1;
                    continue;
                default:
                    break;
                }
                break;
            }

            /* Width */
            if (ch >= '0' && ch <= '9') {
                ch = a2u(ch, &fmt, 10, &(p.width));
            }

            /* We accept 'x.y' format but don't support it completely:
             * we ignore the 'y' digit => this ignores 0-fill
             * size and makes it == width (ie. 'x') */
            if (ch == '.') {
              p.lz = 1;  /* zero-padding */
              /* ignore actual 0-fill size: */
              do {
                ch = *(fmt++);
              } while ((ch >= '0') && (ch <= '9'));
            }

#ifdef PRINTF_SIZE_T_SUPPORT
# ifdef PRINTF_LONG_SUPPORT
            if (ch == 'z') {
                ch = *(fmt++);
                if (sizeof(size_t) == sizeof(unsigned long int))
                    lng = 1;
#  ifdef PRINTF_LONG_LONG_SUPPORT
                else if (sizeof(size_t) == sizeof(unsigned long long int))
                    lng = 2;
#  endif
            } else
# endif
#endif

#ifdef PRINTF_LONG_SUPPORT
            if (ch == 'l') {
                ch = *(fmt++);
                lng = 1;
#ifdef PRINTF_LONG_LONG_SUPPORT
                if (ch == 'l') {
                  ch = *(fmt++);
                  lng = 2;
                }
#endif
            }
#endif
            switch (ch) {
            case 0:
                goto abort;
            case 'u':
                p.base = 10;
#ifdef PRINTF_LONG_SUPPORT
#ifdef PRINTF_LONG_LONG_SUPPORT
                if (2 == lng)
                    ulli2a(va_arg(va, unsigned long long int), &p);
                else
#endif
                  if (1 == lng)
                    uli2a(va_arg(va, unsigned long int), &p);
                else
#endif
                    ui2a(va_arg(va, unsigned int), &p);
                putchw(putp, putf, &p);
                break;
            case 'd':
            case 'i':
                p.base = 10;
#ifdef PRINTF_LONG_SUPPORT
#ifdef PRINTF_LONG_LONG_SUPPORT
                if (2 == lng)
                    lli2a(va_arg(va, long long int), &p);
                else
#endif
                  if (1 == lng)
                    li2a(va_arg(va, long int), &p);
                else
#endif
                    i2a(va_arg(va, int), &p);
                putchw(putp, putf, &p);
                break;
#ifdef SIZEOF_POINTER
            case 'p':
                p.alt = 1;
#ifdef PRINTF_LONG_SUPPORT
# if defined(SIZEOF_INT) && SIZEOF_POINTER <= SIZEOF_INT
                lng = 0;
# elif defined(SIZEOF_LONG) && SIZEOF_POINTER <= SIZEOF_LONG
                lng = 1;
# elif defined(SIZEOF_LONG_LONG) && SIZEOF_POINTER <= SIZEOF_LONG_LONG
                lng = 2;
# endif
#endif
#endif
            case 'x':
            case 'X':
                p.base = 16;
                p.uc = (ch == 'X')?1:0;
#ifdef PRINTF_LONG_SUPPORT
#ifdef PRINTF_LONG_LONG_SUPPORT
                if (2 == lng)
                    ulli2a(va_arg(va, unsigned long long int), &p);
                else
#endif
                  if (1 == lng)
                    uli2a(va_arg(va, unsigned long int), &p);
                else
#endif
                    ui2a(va_arg(va, unsigned int), &p);
                putchw(putp, putf, &p);
                break;
            case 'o':
                p.base = 8;
                ui2a(va_arg(va, unsigned int), &p);
                putchw(putp, putf, &p);
                break;
            case 'c':
                putf(putp, (char)(va_arg(va, int)));
                break;
            case 's':
                p.bf = va_arg(va, char *);
                putchw(putp, putf, &p);
                p.bf = bf;
                break;
            case '%':
                putf(putp, ch);
            default:
                break;
            }
        }
    }
 abort:;
}

#if TINYPRINTF_DEFINE_TFP_PRINTF
static putcf stdout_putf;
static void *stdout_putp;

void init_printf(void *putp, putcf putf__)
{
    stdout_putf = putf;
    stdout_putp = putp;
}

void tfp_printf(char *fmt, ...)
{
    va_list va;
    va_start(va, fmt);
    tfp_format(stdout_putp, stdout_putf, fmt, va);
    va_end(va);
}
#endif

#if TINYPRINTF_DEFINE_TFP_SPRINTF
struct _vsnprintf_putcf_data
{
  size_t dest_capacity;
  char *dest;
  size_t num_chars;
};

static void _vsnprintf_putcf(void *p, char c)
{
  struct _vsnprintf_putcf_data *data = (struct _vsnprintf_putcf_data*)p;
  if (data->num_chars < data->dest_capacity)
    data->dest[data->num_chars] = c;
  data->num_chars ++;
}

int tfp_vsnprintf(char *str, size_t size, const char *format, va_list ap)
{
  struct _vsnprintf_putcf_data data;

  if (size < 1)
    return 0;

  data.dest = str;
  data.dest_capacity = size-1;
  data.num_chars = 0;
  tfp_format(&data, _vsnprintf_putcf, format, ap);

  if (data.num_chars < data.dest_capacity)
    data.dest[data.num_chars] = '\0';
  else
    data.dest[data.dest_capacity] = '\0';

  return data.num_chars;
}

int tfp_snprintf(char *str, size_t size, const char *format, ...)
{
  va_list ap;
  int retval;

  va_start(ap, format);
  retval = tfp_vsnprintf(str, size, format, ap);
  va_end(ap);
  return retval;
}

struct _vsprintf_putcf_data
{
  char *dest;
  size_t num_chars;
};

static void _vsprintf_putcf(void *p, char c)
{
  struct _vsprintf_putcf_data *data = (struct _vsprintf_putcf_data*)p;
  data->dest[data->num_chars++] = c;
}

int tfp_vsprintf(char *str, const char *format, va_list ap)
{
  struct _vsprintf_putcf_data data;
  data.dest = str;
  data.num_chars = 0;
  tfp_format(&data, _vsprintf_putcf, format, ap);
  data.dest[data.num_chars] = '\0';
  return data.num_chars;
}

int tfp_sprintf(char *str, const char *format, ...)
{
  va_list ap;
  int retval;

  va_start(ap, format);
  retval = tfp_vsprintf(str, format, ap);
  va_end(ap);
  return retval;
}
#endif
