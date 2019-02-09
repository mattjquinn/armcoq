.global _start
_start:
  mov r7, #4
  mov r0, #1
  #mov r2, #12
  #ldr r1, =string
  mov r2, #1
  mov r1, #65
  swi 0
  mov r7, #1
  swi 0
  .data
string:
  .ascii "Hello World\n"


#.text
#.global main
#.extern printf
#main:
#        push {ip, lr}
#
#        ldr r0, =string
#        mov r1, #1024
#        bl printf
#
#        pop {ip, pc}
#
#.data
#string: .asciz "The number is: %d\n"
#
