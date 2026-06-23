/*
 * Inputs:
 *   r0 = base address of the array
 *   r1 = number of 32-bit signed elements
 *
 * Sorts the array in ascending order using insertion sort.
 *
 */

_start:
        cmp     r1, #1
        bls     finished            @ Nothing to sort if length <= 1

        mov     r2, #1              @ i = 1

outer_loop:
        cmp     r2, r1
        bhs     finished            @ Stop when i >= length

        ldr     r3, [r0, r2, lsl #2]
                                    @ key = array[i]

        mov     r4, r2              @ j = i

inner_loop:
        cmp     r4, #0
        beq     insert_key

        sub     r5, r4, #1          @ r5 = j - 1
        ldr     r6, [r0, r5, lsl #2]
                                    @ r6 = array[j - 1]

        cmp     r6, r3
        ble     insert_key          @ Stop if array[j - 1] <= key

        str     r6, [r0, r4, lsl #2]
                                    @ array[j] = array[j - 1]

        mov     r4, r5              @ j--
        b       inner_loop

insert_key:
        str     r3, [r0, r4, lsl #2]
                                    @ array[j] = key

        add     r2, r2, #1          @ i++
        b       outer_loop

finished:
        b       finished            @ Halt by looping forever