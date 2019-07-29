#include "attributesForCortexM4.inc"

	.file	"fe25519_mul_u32_asm.S"
	
	.text
	.align  4
	.code   16
	.syntax unified

	.global	fe25519_mul_u32_asm
	.type	fe25519_mul_u32_asm, %function

fe25519_mul_u32_asm:
	@ This multiply-by-word routine is based on Hayato Fujii's code, which is
	@ in turn based on [SantisSigl17].
	@ Source: http://taurus.unicamp.br/bitstream/REPOSIP/332957/1/Fujii_Hayato_M.pdf
	@
	@ r1 holds a 32-bit integer@ [r3-r10] holds a 256-bit integer
	push {r3,r4,r5,r6,r7,r8,r9,r10,r14}
	ldr r3, [r0,#0]
	ldr r4, [r0,#4]
	ldr r5, [r0,#8]
	ldr r6, [r0,#12]
	ldr r7, [r0,#16]
	ldr r8, [r0,#20]
	ldr r9, [r0,#24]
	ldr r10, [r0,#28]
		
	umull r3, r14, r3, r1
	sub r1, r1, #1
	umaal r4, r14, r4, r1
	umaal r5, r14, r5, r1
	umaal r6, r14, r6, r1
	umaal r7, r14, r7, r1
	umaal r8, r14, r8, r1
	umaal r9, r14, r9, r1
	umaal r10, r14, r10, r1
	
	@ reducing r14
	mov r2, #38
	mov r1, #0
	
	umlal r3, r1, r14, r2
	adds r4, r4, r1
	adcs r5, r5, #0
	adcs r6, r6, #0
	adcs r7, r7, #0
	adcs r8, r8, #0
	adcs r9, r9, #0
	adcs r10, r10, #0
	
	str r3, [r0,#0]
	str r4, [r0,#4]
	str r5, [r0,#8]
	str r6, [r0,#12]
	str r7, [r0,#16]
	str r8, [r0,#20]
	str r9, [r0,#24]
	str r10, [r0,#28]
	
	pop {r3,r4,r5,r6,r7,r8,r9,r10,r15}