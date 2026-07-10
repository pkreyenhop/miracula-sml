|| ============================================================================
|| Advent of Code 2025 - Day 1: Secret Entrance (Miracula Idiomatic Solution)
|| ============================================================================

|| ----------------------------------------------------------------------------
|| 1. Helper Operations & Bounded Math
|| ----------------------------------------------------------------------------

|| Miracula standard modulus behaves natively. We force a positive Euclidean modulo 
|| to guarantee positions stay bound within 0-99 when rotating into negative space.
mod100 n = (n mod 100 + 100) mod 100

|| Parses a rotation instruction (e.g., "L68" -> -68, "R48" -> 48)
parseInstruction (dir:distStr) = if dir == 'L' then 0 - numval distStr else numval distStr

|| ----------------------------------------------------------------------------
|| 2. Part 1: Atomic Rotation Jumping
|| ----------------------------------------------------------------------------
|| Tracks only the final positions after each line equation instruction execution.

solvePart1 instructions = countZeros (drop 1 finalPositions)
  where
    || Scan across list generating positions sequentially via lazy foldl style mapping
    finalPositions = foldl nextPos [50] instructions
    nextPos history inst = history ++ [mod100 (last history + inst)]
    
    || Helper to grab the last item of a finite tracking collection
    last (x:[]) = x
    last (x:xs) = last xs
    
    || Count instances landing perfectly on 0
    countZeros []     = 0
    countZeros (x:xs) = if x == 0 then 1 + countZeros xs else countZeros xs

|| ----------------------------------------------------------------------------
|| 3. Part 2: Click-by-Click Zero Crossing Simulation
|| ----------------------------------------------------------------------------
|| Generates an explicit lazy list of every single tick passed through across 
|| the entire puzzle sequence, then counts the overall occurrences of zero.

solvePart2 instructions = countZeros (allTicks 50 instructions)
  where
    || Recurse through instructions producing an overarching lazy stream of steps
    allTicks currentPos []         = []
    allTicks currentPos (inst:ins) = path ++ allTicks nextPos ins
      where
        nextPos = mod100 (currentPos + inst)
        
        || Generate all sequential intermediate cells based on turning direction
        path    = if inst < 0 then [ mod100 (currentPos - tick) | tick <- [1 .. (0 - inst)] ] else [ mod100 (currentPos + tick) | tick <- [1 .. inst] ]
                
    countZeros []     = 0
    countZeros (x:xs) = if x == 0 then 1 + countZeros xs else countZeros xs

|| ----------------------------------------------------------------------------
|| 4. Lazy Main Entrypoint and Stream IO Pipeline (Section 7.2 & 8)
|| ----------------------------------------------------------------------------

main =
  "Advent of Code 2025 - Day 1 Results:\n" ++
  "  Part 1 (Landing stops on 0): " ++ show p1Result ++ "\n" ++
  "  Part 2 (Total times touching 0): " ++ show p2Result ++ "\n"
  where
    || Raw lazy stream file IO read desugared straight into lines of inputs
    rawInput     = read "input.txt"
    parsedLines  = map parseInstruction (lines rawInput)
    
    p1Result     = solvePart1 parsedLines
    p2Result     = solvePart2 parsedLines
