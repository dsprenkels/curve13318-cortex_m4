// Author: Bjoern Haase
// public domain 
//
//  

#include "attributesForCortexM4.inc"

 .align	2
	.global	multiply192x192_asm
	.type	multiply192x192_asm, %function

multiply192x192_asm:
// ######################
// ASM 192x192 :
// ######################
 // START: mul 192x192 Karatsuba, r0 = result ptr, r1,r2 = operand ptr.
 // Adheres to arm eabi conventions.
    push {r0,r1,r2,r4,r5,r6,r7,r14}
    mov r3,r8
    mov r4,r9
    mov r5,r10
    mov r6,r11
    mov r7,r12
    push {r3,r4,r5,r6,r7}
 // START: mul 96x96 Karatsuba with pointer input
 // in1: r1, pX
 // in2: r2, pY
 // result: r2,r3,r4,r5,r6,r7
 // clobbers: r8,r9,r10,r11,r12,r14
    mov r14,r1
    ldm r2,{r2,r3,r4}
    mov r10,r2
    mov r11,r3
    mov r12,r4
    ldm r1,{r0,r1}
 // START: mul 64x64 Refined Karatsuba
 // Input operands in r4,r5 and r2,r3
 // Result in r0,r1,r2,r3
 // Clobbers: r4-r7, r8 and r9 
    mov r6,r3
    mov r4,r0
    sub r6,r2
    sbc r7,r7
    eor r6,r7
    sub r6,r7
    sub r4,r1
    sbc r5,r5
    eor r4,r5
    sub r4,r5
    eor r7,r5
    mov r9,r6
    mov r8,r4
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r4 
 // Clobbers: r2, r5, r6 
    lsr r4,r0,#16
    uxth r0,r0
    lsr r5,r2,#16
    uxth r2,r2
    mov r6,r0
    mul r0,r2
    mul r6,r5
    mul r2,r4
    mul r4,r5
    lsr r5,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r4,r5
    lsr r5,r6,#16
    lsl r2,r6,#16
    add r0,r2
    adc r4,r5
 // End: mul 32x32
 // Result in r0 ,r4 
 // START: mul 32x32
 // Input operands in r3,r1 
 // Result in r2 ,r3 
 // Clobbers: r6, r5, r1 
    uxth r2,r3
    lsr r3,r3,#16
    lsr r6,r1,#16
    uxth r5,r1
    mov r1,r2
    mul r2,r5
    mul r1,r6
    mul r5,r3
    mul r3,r6
    lsr r6,r5,#16
    lsl r5,r5,#16
    add r2,r5
    adc r3,r6
    lsr r6,r1,#16
    lsl r5,r1,#16
    add r2,r5
    adc r3,r6
 // End: mul 32x32
 // Result in r2 ,r3 
    mov r6,#0
    add r2,r4
    adc r3,r6
    mov r4,r8
    mov r5,r9
    mov r8,r0
 // START: mul 32x32
 // Input operands in r4,r5 
 // Result in r1 ,r4 
 // Clobbers: r6, r0, r5 
    uxth r1,r4
    lsr r4,r4,#16
    lsr r6,r5,#16
    uxth r0,r5
    mov r5,r1
    mul r1,r0
    mul r5,r6
    mul r0,r4
    mul r4,r6
    lsr r6,r0,#16
    lsl r0,r0,#16
    add r1,r0
    adc r4,r6
    lsr r6,r5,#16
    lsl r0,r5,#16
    add r1,r0
    adc r4,r6
 // End: mul 32x32
 // Result in r1 ,r4 
    eor r1,r7
    eor r4,r7
    mov r6,#0
    asr r7,r7,#1
    adc r1,r2
    adc r2,r4
    adc r7,r6
    mov r0,r8
    add r1,r0
    adc r2,r3
    adc r3,r7
 // END: mul 64x64 Refined Karatsuba
 // Result in r0,r1,r2,r3
    push {r0,r1}
    mov r0,r14
    ldm r0!,{r5,r6,r7}
    mov r8,r6
    mov r9,r7
    mov r0,r12
 // START: mul 32x32
 // Input operands in r0,r5 
 // Result in r0 ,r1 
 // Clobbers: r4, r5, r6 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r4,r5,#16
    uxth r5,r5
    mov r6,r0
    mul r0,r5
    mul r6,r4
    mul r5,r1
    mul r1,r4
    lsr r4,r5,#16
    lsl r5,r5,#16
    add r0,r5
    adc r1,r4
    lsr r4,r6,#16
    lsl r5,r6,#16
    add r0,r5
    adc r1,r4
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r4,#0
    add r2,r0
    adc r3,r1
    adc r4,r4
    mov r5,r10
 // START: mul 32x32
 // Input operands in r5,r7 
 // Result in r0 ,r1 
 // Clobbers: r7, r5, r6 
    uxth r0,r5
    lsr r1,r5,#16
    lsr r5,r7,#16
    uxth r7,r7
    mov r6,r0
    mul r0,r7
    mul r6,r5
    mul r7,r1
    mul r1,r5
    lsr r5,r7,#16
    lsl r7,r7,#16
    add r0,r7
    adc r1,r5
    lsr r5,r6,#16
    lsl r7,r6,#16
    add r0,r7
    adc r1,r5
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r5,#0
    add r2,r0
    adc r3,r1
    adc r4,r5
    mov r10,r2
    mov r2,r11
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r3,r0
    adc r4,r1
    adc r5,r5
    mov r2,r12
    mov r0,r8
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r2,#0
    add r3,r0
    adc r4,r1
    adc r5,r2
    mov r2,r12
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r4,r0
    adc r5,r1
    pop {r0,r1}
    mov r2,r10
 // END: mul 96x96 

    mov r7,#20
    add r7,r7,r13
    ldm r7!,{r6}
    stm r6!,{r0,r1,r2}
    push {r3,r4,r5}
    ldm r7!,{r1,r2}
    add r1,#12
    add r2,#12
 // START: mul 96x96 Karatsuba with pointer input
 // in1: r1, pX
 // in2: r2, pY
 // result: r2,r3,r4,r5,r6,r7
 // clobbers: r8,r9,r10,r11,r12,r14
    mov r14,r1
    ldm r2,{r2,r3,r4}
    mov r10,r2
    mov r11,r3
    mov r12,r4
    ldm r1,{r0,r1}
 // START: mul 64x64 Refined Karatsuba
 // Input operands in r4,r5 and r2,r3
 // Result in r0,r1,r2,r3
 // Clobbers: r4-r7, r8 and r9 
    mov r6,r3
    mov r4,r0
    sub r6,r2
    sbc r7,r7
    eor r6,r7
    sub r6,r7
    sub r4,r1
    sbc r5,r5
    eor r4,r5
    sub r4,r5
    eor r7,r5
    mov r9,r6
    mov r8,r4
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r4 
 // Clobbers: r2, r5, r6 
    lsr r4,r0,#16
    uxth r0,r0
    lsr r5,r2,#16
    uxth r2,r2
    mov r6,r0
    mul r0,r2
    mul r6,r5
    mul r2,r4
    mul r4,r5
    lsr r5,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r4,r5
    lsr r5,r6,#16
    lsl r2,r6,#16
    add r0,r2
    adc r4,r5
 // End: mul 32x32
 // Result in r0 ,r4 
 // START: mul 32x32
 // Input operands in r3,r1 
 // Result in r2 ,r3 
 // Clobbers: r6, r5, r1 
    uxth r2,r3
    lsr r3,r3,#16
    lsr r6,r1,#16
    uxth r5,r1
    mov r1,r2
    mul r2,r5
    mul r1,r6
    mul r5,r3
    mul r3,r6
    lsr r6,r5,#16
    lsl r5,r5,#16
    add r2,r5
    adc r3,r6
    lsr r6,r1,#16
    lsl r5,r1,#16
    add r2,r5
    adc r3,r6
 // End: mul 32x32
 // Result in r2 ,r3 
    mov r6,#0
    add r2,r4
    adc r3,r6
    mov r4,r8
    mov r5,r9
    mov r8,r0
 // START: mul 32x32
 // Input operands in r4,r5 
 // Result in r1 ,r4 
 // Clobbers: r6, r0, r5 
    uxth r1,r4
    lsr r4,r4,#16
    lsr r6,r5,#16
    uxth r0,r5
    mov r5,r1
    mul r1,r0
    mul r5,r6
    mul r0,r4
    mul r4,r6
    lsr r6,r0,#16
    lsl r0,r0,#16
    add r1,r0
    adc r4,r6
    lsr r6,r5,#16
    lsl r0,r5,#16
    add r1,r0
    adc r4,r6
 // End: mul 32x32
 // Result in r1 ,r4 
    eor r1,r7
    eor r4,r7
    mov r6,#0
    asr r7,r7,#1
    adc r1,r2
    adc r2,r4
    adc r7,r6
    mov r0,r8
    add r1,r0
    adc r2,r3
    adc r3,r7
 // END: mul 64x64 Refined Karatsuba
 // Result in r0,r1,r2,r3
    push {r0,r1}
    mov r0,r14
    ldm r0!,{r5,r6,r7}
    mov r8,r6
    mov r9,r7
    mov r0,r12
 // START: mul 32x32
 // Input operands in r0,r5 
 // Result in r0 ,r1 
 // Clobbers: r4, r5, r6 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r4,r5,#16
    uxth r5,r5
    mov r6,r0
    mul r0,r5
    mul r6,r4
    mul r5,r1
    mul r1,r4
    lsr r4,r5,#16
    lsl r5,r5,#16
    add r0,r5
    adc r1,r4
    lsr r4,r6,#16
    lsl r5,r6,#16
    add r0,r5
    adc r1,r4
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r4,#0
    add r2,r0
    adc r3,r1
    adc r4,r4
    mov r5,r10
 // START: mul 32x32
 // Input operands in r5,r7 
 // Result in r0 ,r1 
 // Clobbers: r7, r5, r6 
    uxth r0,r5
    lsr r1,r5,#16
    lsr r5,r7,#16
    uxth r7,r7
    mov r6,r0
    mul r0,r7
    mul r6,r5
    mul r7,r1
    mul r1,r5
    lsr r5,r7,#16
    lsl r7,r7,#16
    add r0,r7
    adc r1,r5
    lsr r5,r6,#16
    lsl r7,r6,#16
    add r0,r7
    adc r1,r5
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r5,#0
    add r2,r0
    adc r3,r1
    adc r4,r5
    mov r10,r2
    mov r2,r11
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r3,r0
    adc r4,r1
    adc r5,r5
    mov r2,r12
    mov r0,r8
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r2,#0
    add r3,r0
    adc r4,r1
    adc r5,r2
    mov r2,r12
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r4,r0
    adc r5,r1
    pop {r0,r1}
    mov r2,r10
 // END: mul 96x96 

    pop {r6,r7}
    add r0,r6
    adc r1,r7
    pop {r6}
    adc r2,r6
    mov r6,#0
    adc r3,r6
    adc r4,r6
    adc r5,r6
    push {r0,r1,r2,r3,r4,r5}
    ldr r6,[SP,#48]
    ldm r6!,{r0,r1,r2,r3,r4,r5}
    sub r3,r0
    sbc r4,r1
    sbc r5,r2
    sbc r7,r7
    eor r3,r7
    eor r4,r7
    eor r5,r7
    sub r3,r7
    sbc r4,r7
    sbc r5,r7
    mov r10,r3
    mov r11,r4
    mov r12,r5
    ldr r6,[SP,#52]
    ldm r6!,{r0,r1,r2,r3,r4,r5}
    sub r0,r3
    sbc r1,r4
    sbc r2,r5
    sbc r6,r6
    eor r0,r6
    eor r1,r6
    eor r2,r6
    sub r0,r6
    sbc r1,r6
    sbc r2,r6
    eor r7,r6
    push {r7}
 // START: mul 96x96 with inputs in regs
 // in1: r10,r11,r12
 // in2: r0,r1,r2 
 // result: r2,r3,r4,r5,r6,r7
 // clobbers: r8,r9,r10,r11,r12,r14
    mov r14,r1
    push {r0,r2}
    mov r2,r10
    mov r3,r11
 // START: mul 64x64 Refined Karatsuba
 // Input operands in r4,r5 and r2,r3
 // Result in r0,r1,r2,r3
 // Clobbers: r4-r7, r8 and r9 
    mov r6,r3
    mov r4,r0
    sub r6,r2
    sbc r7,r7
    eor r6,r7
    sub r6,r7
    sub r4,r1
    sbc r5,r5
    eor r4,r5
    sub r4,r5
    eor r7,r5
    mov r9,r6
    mov r8,r4
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r4 
 // Clobbers: r2, r5, r6 
    lsr r4,r0,#16
    uxth r0,r0
    lsr r5,r2,#16
    uxth r2,r2
    mov r6,r0
    mul r0,r2
    mul r6,r5
    mul r2,r4
    mul r4,r5
    lsr r5,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r4,r5
    lsr r5,r6,#16
    lsl r2,r6,#16
    add r0,r2
    adc r4,r5
 // End: mul 32x32
 // Result in r0 ,r4 
 // START: mul 32x32
 // Input operands in r3,r1 
 // Result in r2 ,r3 
 // Clobbers: r6, r5, r1 
    uxth r2,r3
    lsr r3,r3,#16
    lsr r6,r1,#16
    uxth r5,r1
    mov r1,r2
    mul r2,r5
    mul r1,r6
    mul r5,r3
    mul r3,r6
    lsr r6,r5,#16
    lsl r5,r5,#16
    add r2,r5
    adc r3,r6
    lsr r6,r1,#16
    lsl r5,r1,#16
    add r2,r5
    adc r3,r6
 // End: mul 32x32
 // Result in r2 ,r3 
    mov r6,#0
    add r2,r4
    adc r3,r6
    mov r4,r8
    mov r5,r9
    mov r8,r0
 // START: mul 32x32
 // Input operands in r4,r5 
 // Result in r1 ,r4 
 // Clobbers: r6, r0, r5 
    uxth r1,r4
    lsr r4,r4,#16
    lsr r6,r5,#16
    uxth r0,r5
    mov r5,r1
    mul r1,r0
    mul r5,r6
    mul r0,r4
    mul r4,r6
    lsr r6,r0,#16
    lsl r0,r0,#16
    add r1,r0
    adc r4,r6
    lsr r6,r5,#16
    lsl r0,r5,#16
    add r1,r0
    adc r4,r6
 // End: mul 32x32
 // Result in r1 ,r4 
    eor r1,r7
    eor r4,r7
    mov r6,#0
    asr r7,r7,#1
    adc r1,r2
    adc r2,r4
    adc r7,r6
    mov r0,r8
    add r1,r0
    adc r2,r3
    adc r3,r7
 // END: mul 64x64 Refined Karatsuba
 // Result in r0,r1,r2,r3
    pop {r5,r7}
    push {r0,r1}
    mov r9,r7
    mov r0,r12
 // START: mul 32x32
 // Input operands in r0,r5 
 // Result in r0 ,r1 
 // Clobbers: r4, r5, r6 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r4,r5,#16
    uxth r5,r5
    mov r6,r0
    mul r0,r5
    mul r6,r4
    mul r5,r1
    mul r1,r4
    lsr r4,r5,#16
    lsl r5,r5,#16
    add r0,r5
    adc r1,r4
    lsr r4,r6,#16
    lsl r5,r6,#16
    add r0,r5
    adc r1,r4
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r4,#0
    add r2,r0
    adc r3,r1
    adc r4,r4
    mov r5,r10
 // START: mul 32x32
 // Input operands in r5,r7 
 // Result in r0 ,r1 
 // Clobbers: r7, r5, r6 
    uxth r0,r5
    lsr r1,r5,#16
    lsr r5,r7,#16
    uxth r7,r7
    mov r6,r0
    mul r0,r7
    mul r6,r5
    mul r7,r1
    mul r1,r5
    lsr r5,r7,#16
    lsl r7,r7,#16
    add r0,r7
    adc r1,r5
    lsr r5,r6,#16
    lsl r7,r6,#16
    add r0,r7
    adc r1,r5
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r5,#0
    add r2,r0
    adc r3,r1
    adc r4,r5
    mov r10,r2
    mov r2,r11
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r3,r0
    adc r4,r1
    adc r5,r5
    mov r2,r12
    mov r0,r14
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    mov r2,#0
    add r3,r0
    adc r4,r1
    adc r5,r2
    mov r2,r12
    mov r0,r9
 // START: mul 32x32
 // Input operands in r0,r2 
 // Result in r0 ,r1 
 // Clobbers: r2, r6, r7 
    lsr r1,r0,#16
    uxth r0,r0
    lsr r6,r2,#16
    uxth r2,r2
    mov r7,r0
    mul r0,r2
    mul r7,r6
    mul r2,r1
    mul r1,r6
    lsr r6,r2,#16
    lsl r2,r2,#16
    add r0,r2
    adc r1,r6
    lsr r6,r7,#16
    lsl r2,r7,#16
    add r0,r2
    adc r1,r6
 // End: mul 32x32
 // Result in r0 ,r1 
    add r4,r0
    adc r5,r1
    pop {r0,r1}
    mov r2,r10
 // END: mul 96x96_regs 

    pop {r7}
    eor r0,r7
    eor r1,r7
    eor r2,r7
    eor r3,r7
    eor r4,r7
    eor r5,r7
    mov r8,r7
    asr r7,r7,#1
    mov r10,r5
    pop {r5,r6,r7}
    adc r0,r5
    adc r1,r6
    adc r2,r7
    adc r3,r5
    adc r4,r6
    mov r9,r4
    mov r4,r10
    adc r4,r7
    mov r10,r4
    mov r6,#0
    mov r7,r8
    adc r7,r6
    mov r11,r7
    asr r7,r7,#32
    mov r8,r7
    ldr r5,[SP,#32]
    ldm r5!,{r6,r7}
    add r0,r6
    adc r1,r7
    ldm r5!,{r6}
    stm r5!,{r0,r1}
    adc r2,r6
    stm r5!,{r2}
    pop {r0,r1,r2}
    adc r3,r0
    mov r4,r9
    adc r4,r1
    mov r6,r10
    adc r6,r2
    stm r5!,{r3,r4,r6}
    mov r4,r11
    mov r6,r8
    adc r0,r4
    adc r1,r6
    adc r2,r6
    stm r5!,{r0,r1,r2}
    pop {r3,r4,r5,r6,r7}
    mov r8,r3
    mov r9,r4
    mov r10,r5
    mov r11,r6
    mov r12,r7
    add SP,#12
    pop {r4,r5,r6,r7,r15}
//Cycle Count ASM-Version of 192x192 (Cortex M0): 827 (719 instructions).
