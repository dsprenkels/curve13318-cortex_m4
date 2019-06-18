// Implementation of multiplication of 256 bit value with uint16 value
//
// B. Haase, Endress + Hauser Conducta GmbH & Ko. KG
// public domain.
//
// gnu assembler format.
//
// Generated and tested with C++ functions in the test subdirectory.
//
// ATTENTION:
// Not yet tested on target hardware.

#include "attributesForCortexM4.inc"

	.code	16
	
	.file	"cortex_m0_fe25519_mpy_uint16.s"
	
	.text
	.align	2

	.global	fe25519_mpyWith_uint16_asm
	.code	16
	.thumb_func
	.type	fe25519_mpyWith_uint16_asm, %function

fe25519_mpyWith_uint16_asm:
	
// ######################
// ASM fe25519 mpy with uint16:
// ######################
// Start of MPY with uint16. In: ptr to data in r0. Value to multiply (16 bits!) in r1.
    push {r4,r5,r6,r14}
    mov r6,#0
    ldr r2,[r0,#28]
    uxth r3,r2
    lsr r4,r2,#16
    mul r3,r1
    mul r4,r1
    lsl r2,r4,#16
    lsr r4,r4,#16
    add r3,r2
    adc r4,r6
    lsl r2,r3,#1
    lsr r2,r2,#1
    str r2,[r0,#28]
    lsr r3,r3,#31
    lsl r4,r4,#1
    orr r3,r4
    mov r4,#19
    mul r3,r4
    mov r4,#0
    ldr r2,[r0,#0]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r3,r2
    adc r4,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r3,r2
    adc r4,r5
    str r3,[r0,#0]
    mov r3,#0
    ldr r2,[r0,#4]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r4,r2
    adc r3,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r4,r2
    adc r3,r5
    str r4,[r0,#4]
    mov r4,#0
    ldr r2,[r0,#8]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r3,r2
    adc r4,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r3,r2
    adc r4,r5
    str r3,[r0,#8]
    mov r3,#0
    ldr r2,[r0,#12]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r4,r2
    adc r3,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r4,r2
    adc r3,r5
    str r4,[r0,#12]
    mov r4,#0
    ldr r2,[r0,#16]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r3,r2
    adc r4,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r3,r2
    adc r4,r5
    str r3,[r0,#16]
    mov r3,#0
    ldr r2,[r0,#20]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r4,r2
    adc r3,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r4,r2
    adc r3,r5
    str r4,[r0,#20]
    mov r4,#0
    ldr r2,[r0,#24]
    lsr r5,r2,#16
    uxth r2,r2
    mul r2,r1
    mul r5,r1
    add r3,r2
    adc r4,r6
    lsl r2,r5,#16
    lsr r5,r5,#16
    add r3,r2
    adc r4,r5
    str r3,[r0,#24]
    mov r3,#0
    ldr r2,[r0,#28]
    add r4,r2
    str r4,[r0,#28]
    pop {r4,r5,r6,r15}
	    			
	.size	fe25519_mpyWith_uint16_asm, .-fe25519_mpyWith_uint16_asm
		    	
