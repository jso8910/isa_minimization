// ARM32 Binary Search
// Inputs:
//   R0 = The value being searched for
// Outputs:
//   R1 = The address of the value if found, or -1 if not found
// Static instruction count: 17

binary_search:

    MOV R2, #0          // R2 (low) = 0
    MOV R3, #63         // R3 (high) = 63

search_loop:
    CMP R2, R3          // Check if low > high
    BGT not_found       // If low > high, the value is not in the array

    ADD R4, R2, R3      // R4 = low + high
    LSR R4, R4, #1      // R4 (mid) = (low + high) / 2

    LDRB R5, [R4]       // Load the 8-bit value at address 'mid' into R5
                        // (Address and index are identical here)

    CMP R5, R0          // Compare memory[mid] (R5) with the search value (R0)
    BEQ found           // If equal, we found the target!

    BLT search_right    // If memory[mid] < target, search the right half

search_left:
    SUB R3, R4, #1      // high = mid - 1
    B search_loop       // Repeat the loop

search_right:
    ADD R2, R4, #1      // low = mid + 1
    B search_loop       // Repeat the loop

found:
    MOV R1, R4          // Set R1 to the memory address (mid) where value was found
    B end_search

not_found:
    MVN R1, #0          // Set R1 to -1 (0xFFFFFFFF) to indicate value not found

end_search:
