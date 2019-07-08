#define CRYPTO_HAS_ASM_FE25519_ADD
#define CRYPTO_HAS_ASM_FE25519_MUL
#define CRYPTO_HAS_ASM_FE25519_SQUARE
#define CRYPTO_HAS_ASM_REDUCE_25519
#include "fe25519/fe25519.h"

/// Used for fast randomization of field elements. Use 16 bit randomization constant
/// since it's easy and fast to implement and it's repeated application is still considered
/// to make statistical analysis very hard.
void
fe25519_mpyWith_uint16_asm(
    fe25519*       inOut,
    const uint16_t   valU16
);
