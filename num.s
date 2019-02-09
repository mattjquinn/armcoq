.text
.global main
.extern printf
main:
        push {ip, lr}

        ldr r0, =string
        mov r1, #1024
        bl printf

        pop {ip, pc}

.data
string: .asciz "The number is: %d\n"

