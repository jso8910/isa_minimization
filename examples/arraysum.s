/*
 * Inputs:
 *   r0 = address of the first array element
 *   r1 = number of 32-bit elements
 *
 * Output:
 *   r2 = sum of the elements
 *
 * Clobbers:
 *   r0, r1, r3
 */

_start:
        mov     r2, #0              @ sum = 0

sum_loop:
        cmp     r1, #0
        beq     finished            @ Stop once no elements remain

        ldr     r3, [r0]            @ Load current array element
        add     r2, r2, r3          @ sum += element

        add     r0, r0, #4          @ Advance to next 32-bit element
        sub     r1, r1, #1          @ remaining--

        b       sum_loop

finished:
        b       finished