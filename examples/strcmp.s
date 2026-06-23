/*
 * Inputs:
 *   r0 = address of first null-terminated string
 *   r1 = address of second null-terminated string
 *
 * Output:
 *   r2 = -1 if string1 < string2
 *        0 if string1 == string2
 *        1 if string1 > string2
 *
 * Comparison is lexicographic using unsigned byte values.
 *
 * Clobbers:
 *   r2-r4
 */
_start:
compare_loop:
        ldrb    r3, [r0]            @ r3 = current byte of string1
        ldrb    r4, [r1]            @ r4 = current byte of string2

        cmp     r3, r4
        blo     string1_less
        bhi     string1_greater

        cmp     r3, #0              @ Equal bytes; check for null terminator
        beq     strings_equal

        add     r0, r0, #1          @ Advance string1 pointer
        add     r1, r1, #1          @ Advance string2 pointer
        b       compare_loop

string1_less:
        mov     r2, #-1
        b       finished

string1_greater:
        mov     r2, #1
        b       finished

strings_equal:
        mov     r2, #0

finished:
        b       finished            @ Halt by looping forever