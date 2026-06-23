/*
 * Matrix multiplication:
 *
 *     C = A * B
 *
 * Inputs:
 *   r0 = address of A
 *   r1 = address of B
 *   r2 = address of output C
 *   r3 = M: number of rows in A
 *   r4 = N: columns in A / rows in B
 *   r5 = P: number of columns in B
 *
 * Matrix dimensions:
 *   A is M x N
 *   B is N x P
 *   C is M x P
 *
 * All elements are 32-bit integers stored in row-major order.
 *
 * Clobbers:
 *   r6-r12, lr
 *
 * Multiplication and accumulation wrap modulo 2^32.
 */

_start:
        mov     r6, #0              @ i = 0

row_loop:
        cmp     r6, r3
        bhs     finished            @ Stop when i >= M

        mov     r7, #0              @ j = 0

column_loop:
        cmp     r7, r5
        bhs     next_row            @ Move to next row when j >= P

        mov     r9, #0              @ sum = 0
        mov     r8, #0              @ k = 0

        /*
         * r10 = address of A[i][0]
         *
         * Offset in elements:
         *     i * N
         */
        mul     r12, r6, r4
        add     r10, r0, r12, lsl #2

        /*
         * r11 = address of B[0][j]
         *
         * Offset in elements:
         *     j
         */
        add     r11, r1, r7, lsl #2

dot_product_loop:
        cmp     r8, r4
        bhs     store_result        @ Stop when k >= N

        ldr     r12, [r10], #4      @ r12 = A[i][k]
                                    @ Advance to A[i][k + 1]

        ldr     lr, [r11]           @ lr = B[k][j]

        mla     r9, r12, lr, r9     @ sum += A[i][k] * B[k][j]

        /*
         * Advance downward by one row of B.
         *
         * Each row of B contains P elements, so advance
         * by P * 4 bytes.
         */
        add     r11, r11, r5, lsl #2

        add     r8, r8, #1          @ k++
        b       dot_product_loop

store_result:
        /*
         * Compute the element offset of C[i][j]:
         *
         *     i * P + j
         */
        mul     r12, r6, r5
        add     r12, r12, r7

        str     r9, [r2, r12, lsl #2]
                                    @ C[i][j] = sum

        add     r7, r7, #1          @ j++
        b       column_loop

next_row:
        add     r6, r6, #1          @ i++
        b       row_loop

finished:
        b       finished            @ Halt by looping forever