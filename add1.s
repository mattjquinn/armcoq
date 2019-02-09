.global _start
main:
_start:
mov  r6, #5                     @ number to go up to
mov  r1, #0                     @ initial value
mov  r2, #1                     @ counter

_loop:
add  r1, r1, r2
b _write                        @print the value

_write:
push {r1, r2, r6, lr}
add  r3, r1, #48
ldr  r0, =character
str  r3, [r0]
mov r7,#4                       @ syscall for output
mov r0,#1                       @ output stream for R1
ldr r1, =character
mov r2,#1
swi 0
pop {r1, r2, r6, lr}
cmp r1,r6                       @ compare if the value is equal to 'n'
bne _loop                       @ if less than, then add again and print

end:
mov R7,#1                       @ syscall for exit
swi 0

.data
character:
.word 0
