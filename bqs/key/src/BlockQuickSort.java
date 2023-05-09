public class BlockQuickSort {

    private static final int BLOCKSIZE = 2; // \paper(128)
    private static final int IS_THRESH = 3; // \paper(16) must be a minimum of 3, since we use 3 elements for pivot selection
    private static final int STACK_SIZE = 10; // \paper(80)
    private static final int DEPTH_STACK_SIZE = 10; // \paper(40)

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length;
      @ requires (originalEnd - originalBegin) >= 1;
      @ requires originalBegin <= pivotPosition && pivotPosition < originalEnd;
      @ ensures array.length == \old(array.length);
      @
      @ // The resulting pivot is inside the range [originalBegin, originalEnd).
      @ ensures originalBegin <= \result && \result < originalEnd;
      @ ensures array[\result] == \old(array[pivotPosition]);
      @
      @ // Values inside the range [originalBegin, \result] are smaller or equal than array[\result].
      @ ensures (\forall int i; originalBegin <= i && i <= \result; array[i] <= array[\result]);
      @ // Values inside the range [\result, originalEnd) are greater or equal than array[\result].
      @ ensures (\forall int i; \result <= i && i < originalEnd; array[\result] <= array[i]);
      @
      @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
      @ ensures permutation(array, \old(array), originalBegin, originalEnd);
      @
      @ assignable array[originalBegin .. originalEnd-1];
      @*/
    public static int hoareBlockPartition(
            int[] array,
            int originalBegin,
            int originalEnd,
            int pivotPosition) {
        int[] indexL = new int[BLOCKSIZE];
        int[] indexR = new int[BLOCKSIZE];

        int begin = originalBegin;
        int end = originalEnd;

        int last = end - 1;
        int pivot = array[pivotPosition];
        swap(array, pivotPosition, last);
        pivotPosition = last;
        last--;

        int numLeft = 0;
        int numRight = 0;
        int startLeft = 0;
        int startRight = 0;
        int num = 0;

        if (last - begin + 1 > 2 * BLOCKSIZE) {
            /*@ loop_invariant originalBegin <= begin && begin <= last && last < originalEnd - 1;
              @ loop_invariant 0 <= numLeft && numLeft <= BLOCKSIZE;
              @ loop_invariant 0 <= numRight && numRight <= BLOCKSIZE;
              @ loop_invariant 0 <= startLeft && startLeft <= BLOCKSIZE && startLeft + numLeft <= BLOCKSIZE;
              @ loop_invariant 0 <= startRight && startRight <= BLOCKSIZE && startRight + numRight <= BLOCKSIZE;
              @ loop_invariant 0 <= num && num <= BLOCKSIZE;
              @ loop_invariant numRight == 0 || numLeft == 0;
              @ loop_invariant array[originalEnd - 1] == \old(array[pivotPosition]);
              @ 
              @ loop_invariant (\exists int i; 0 <= i && i < (originalEnd - originalBegin); begin == originalBegin + i * BLOCKSIZE);
              @ loop_invariant (\exists int i; 0 <= i && i < (originalEnd - originalBegin); last == originalEnd - 2 - i * BLOCKSIZE);
              @
              @ loop_invariant (\forall int i; 0 <= i && i < BLOCKSIZE; 0 <= indexL[i] && indexL[i] < BLOCKSIZE);
              @ loop_invariant (\forall int i; 0 <= i && i < numLeft; indexL[startLeft + i] < last - begin && pivot <= array[begin + indexL[startLeft + i]]);
              @ loop_invariant (\forall int i; 0 <= i && i < startLeft + numLeft - 1; indexL[i] < indexL[i + 1]);
              @ loop_invariant (numLeft != 0) ==> numLeft == (\num_of int i; startLeft <= i && i < BLOCKSIZE; pivot <= array[begin + i]);
              @
              @ loop_invariant (\forall int i; 0 <= i && i < BLOCKSIZE; 0 <= indexR[i] && indexR[i] < BLOCKSIZE);
              @ loop_invariant (\forall int i; 0 <= i && i < numRight; indexR[startRight + i] < last - begin && array[last - indexR[startRight + i]] <= pivot);
              @ loop_invariant (\forall int i; 0 <= i && i < startRight + numRight - 1; indexR[i] < indexR[i + 1]);
              @ loop_invariant (numRight != 0) ==> numRight == (\num_of int i; startRight <= i && i < BLOCKSIZE; array[last - i] <= pivot);
              @
              @ // The elements in the range [originalBegin, begin + indexL[startLeft]) are less than or equal pivot
              @ loop_invariant (numLeft == 0) ==> (\forall int i; originalBegin <= i && i < begin; array[i] <= pivot);
              @ loop_invariant (numLeft != 0) ==> (\forall int i; originalBegin <= i && i < begin + indexL[startLeft]; array[i] <= pivot);
              @
              @ // The elements in the range (last - indexR[startRight], originalEnd) are greater than or equal pivot 
              @ loop_invariant (numRight == 0) ==> (\forall int i; last < i && i < originalEnd; pivot <= array[i]);
              @ loop_invariant (numRight != 0) ==> (\forall int i; last - indexR[startRight] < i && i < originalEnd; pivot <= array[i]);
              @
              @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
              @ loop_invariant permutation(array, \old(array), originalBegin, originalEnd);
              @
              @ assignable array[(begin > originalBegin ? begin : originalBegin) .. (begin + BLOCKSIZE - 1 > originalEnd - 2 ? originalEnd - 2 : begin + BLOCKSIZE - 1)], 
              @            array[(last - BLOCKSIZE - 1 > originalBegin ? last - BLOCKSIZE - 1 : originalBegin) .. (last < originalEnd - 2 ? last : originalEnd - 2)], 
              @               last, begin, numLeft, numRight, startLeft, startRight, num,
              @               indexL[0 .. BLOCKSIZE - 1], indexR[0 .. BLOCKSIZE - 1];
              @
              @ decreases last - begin;
              @*/
            while (last - begin + 1 > 2 * BLOCKSIZE) {

                if (numLeft == 0) {
                    startLeft = 0;

                    //@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                    //@ // Maintain numLeft count
                    //@ loop_invariant numLeft == (\num_of int k; 0 <= k && k < j; pivot <= array[begin + k]);
                    //@ // Maintain indexL array
                    //@ loop_invariant (\forall int k; 0 <= k && k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
                    //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
                    //@ // Maintain sorted indexL
                    //@ loop_invariant (\forall int k; 0 <= k && k < numLeft - 1; indexL[k] < indexL[k + 1]);
                    //@
                    //@ assignable numLeft, indexL[0 .. BLOCKSIZE - 1], j;
                    //@ decreases BLOCKSIZE - j;
                    for (int j = 0; j < BLOCKSIZE; j++) {
                        indexL[numLeft] = j;
                        numLeft += array[begin + j] >= pivot ? 1 : 0;
                    }
                }
                if (numRight == 0) {
                    startRight = 0;
                    //@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                    //@ // Maintain numRight count
                    //@ loop_invariant numRight == (\num_of int k; 0 <= k && k < j; array[last - k] <= pivot);
                    //@ // Maintain indexR array
                    //@ loop_invariant (\forall int k; 0 <= k && k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
                    //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
                    //@ // Maintain sorted indexR
                    //@ loop_invariant (\forall int k; 0 <= k && k < numRight - 1; indexR[k] < indexR[k + 1]);
                    //@
                    //@ assignable numRight, indexR[0 .. BLOCKSIZE - 1], j;
                    //@ decreases BLOCKSIZE - j;
                    for (int j = 0; j < BLOCKSIZE; j++) {
                        indexR[numRight] = j;
                        numRight += pivot >= array[last - j] ? 1 : 0;
                    }
                }

                num = min(numLeft, numRight);
                if (num > 0) {
                    //@ loop_invariant 0 <= j && j <= num;
                    //@ 
                    //@ // Values inside the range [originalBegin, begin + indexL[startLeft + j]) are less than or equal to pivot.
                    //@ loop_invariant (\forall int i; originalBegin <= i && i < begin + indexL[startLeft]; array[i] <= pivot);
                    //@ loop_invariant j > 0 ==> (\forall int i; originalBegin <= i && i <= begin + indexL[startLeft + j - 1]; array[i] <= pivot);
                    //@
                    //@ // Values inside the range (last - indexR[startRight - j], originalEnd) are greater than or equal to pivot.
                    //@ loop_invariant (\forall int i; last - indexR[startRight] < i && i < originalEnd; pivot <= array[i]);
                    //@ loop_invariant j > 0 ==> (\forall int i; last - indexR[startRight + j - 1] <= i && i < originalEnd; pivot <= array[i]);
                    //@
                    //@ // All values indexed by indexL[startLeft + j .. startLeft + numLeft] are greater than or equal to pivot.
                    //@ loop_invariant (\forall int i; startLeft + j <= i && i < startLeft + numLeft; pivot <= array[begin + indexL[i]]);
                    //@
                    //@ // All values indexed by indexR[startRight + j .. startRight + numRight] are less than or equal to pivot.
                    //@ loop_invariant (\forall int i; startRight + j <= i && i < startRight + numRight; array[last - indexR[i]] <= pivot);
                    //@
                    //@ // Values inside the range [begin, last] are a valid permutation.
                    //@ loop_invariant (\forall int i; begin <= i && i < last + 1; (\num_of int k; begin <= k && k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k && k < last + 1; array[i] == \old(array[k])));
                    //@
                    //@ assignable array[begin + indexL[startLeft] .. begin + indexL[startLeft + num - 1]], array[last - indexR[startRight + num - 1] .. last - indexR[startRight]], j;
                    //@ decreases num - j;
                    for (int j = 0; j < num; j++) {
                        swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
                    }
                }

                numLeft -= num;
                numRight -= num;
                startLeft += num;
                startRight += num;
                begin += (numLeft == 0) ? BLOCKSIZE : 0;
                last -= (numRight == 0) ? BLOCKSIZE : 0;
            }
        }

        int shiftR = 0, shiftL = 0;
        if (numRight == 0 && numLeft == 0) {
            shiftL = ((last - begin) + 1) / 2;
            shiftR = (last - begin) + 1 - shiftL;
            startLeft = 0;
            startRight = 0;
            //@ loop_invariant 0 <= j && j <= shiftL;
            //@ loop_invariant 0 <= numLeft && numLeft <= j;
            //@ loop_invariant 0 <= numRight && numRight <= j;
            //@
            //@ // Maintain numLeft count
            //@ loop_invariant numLeft == (\num_of int k; 0 <= k && k < j; pivot <= array[begin + k]);
            //@ // Maintain numRight count
            //@ loop_invariant numRight == (\num_of int k; 0 <= k && k < j; array[last - k] <= pivot);
            //@
            //@ // Maintain indexL array
            //@ loop_invariant (\forall int k; 0 <= k && k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
            //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
            //@ // Maintain indexR array
            //@ loop_invariant (\forall int k; 0 <= k && k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
            //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
            //@
            //@ // Maintain sorted indexL
            //@ loop_invariant (\forall int k; 0 <= k && k < numLeft - 1; indexL[k] < indexL[k + 1]);
            //@ // Maintain sorted indexR
            //@ loop_invariant (\forall int k; 0 <= k && k < numRight - 1; indexR[k] < indexR[k + 1]);
            //@
            //@ decreases shiftL - j;
            //@ assignable indexL[0 .. shiftL - 1], numLeft, indexR[0 .. shiftL - 1], numRight, j;
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
            if (shiftL < shiftR) {
                indexR[numRight] = shiftR - 1;
                numRight += pivot >= array[last - shiftR + 1] ? 1 : 0;
            }
        } else if (numRight != 0) {
            shiftL = (last - begin) - BLOCKSIZE + 1;
            shiftR = BLOCKSIZE;
            startLeft = 0;
            //@ loop_invariant 0 <= j && j <= shiftL;
            //@ // Maintain numLeft count
            //@ loop_invariant numLeft == (\num_of int k; 0 <= k && k < j; pivot <= array[begin + k]);
            //@ // Maintain indexL array
            //@ loop_invariant (\forall int k; 0 <= k && k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
            //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
            //@ // Maintain sorted indexL
            //@ loop_invariant (\forall int k; 0 <= k && k < numLeft - 1; indexL[k] < indexL[k + 1]);
            //@
            //@ assignable numLeft, indexL[0 .. shiftL - 1], j;
            //@ decreases shiftL - j;
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;
            //@ loop_invariant 0 <= j && j <= shiftR;
            //@ // Maintain numRight count
            //@ loop_invariant numRight == (\num_of int k; 0 <= k && k < j; array[last - k] <= pivot);
            //@ // Maintain indexR array
            //@ loop_invariant (\forall int k; 0 <= k && k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
            //@ loop_invariant (\forall int k; 0 <= k && k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
            //@ // Maintain sorted indexR
            //@ loop_invariant (\forall int k; 0 <= k && k < numRight - 1; indexR[k] < indexR[k + 1]);
            //@
            //@ assignable numRight, indexR[0 .. shiftR - 1], j;
            //@ decreases shiftR - j;
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
        }

        num = min(numLeft, numRight);
        if (num > 0) {
            //@ loop_invariant 0 <= j && j <= num;
            //@ 
            //@ // Values inside the range [originalBegin, begin + indexL[startLeft + j]) are less than or equal to pivot.
            //@ loop_invariant (\forall int i; originalBegin <= i && i < begin + indexL[startLeft]; array[i] <= pivot);
            //@ loop_invariant j > 0 ==> (\forall int i; originalBegin <= i && i <= begin + indexL[startLeft + j - 1]; array[i] <= pivot);
            //@
            //@ // Values inside the range (last - indexR[startRight - j], originalEnd) are greater than or equal to pivot.
            //@ loop_invariant (\forall int i; last - indexR[startRight] < i && i < originalEnd; pivot <= array[i]);
            //@ loop_invariant j > 0 ==> (\forall int i; last - indexR[startRight + j - 1] <= i && i < originalEnd; pivot <= array[i]);
            //@
            //@ // All values indexed by indexL[startLeft + j .. startLeft + numLeft] are greater than or equal to pivot.
            //@ loop_invariant (\forall int i; startLeft + j <= i && i < startLeft + numLeft; pivot <= array[begin + indexL[i]]);
            //@
            //@ // All values indexed by indexR[startRight + j .. startRight + numRight] are less than or equal to pivot.
            //@ loop_invariant (\forall int i; startRight + j <= i && i < startRight + numRight; array[last - indexR[i]] <= pivot);
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ loop_invariant (\forall int i; begin <= i && i < last + 1; (\num_of int k; begin <= k && k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k && k < last + 1; array[i] == \old(array[k])));
            //@
            //@ assignable array[begin + indexL[startLeft] .. begin + indexL[startLeft + num - 1]], array[last - indexR[startRight + num - 1] .. last - indexR[startRight]], j;
            //@ decreases num - j;
            for (int j = 0; j < num; j++) {
                swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
            }
        }

        numLeft -= num;
        numRight -= num;
        startLeft += num;
        startRight += num;
        begin += (numLeft == 0) ? shiftL : 0;
        last -= (numRight == 0) ? shiftR : 0;

        if (numLeft != 0) {
            int lowerI = startLeft + numLeft - 1;
            int upper = last - begin;

            //@ loop_invariant 0 <= startLeft && startLeft - 1 <= lowerI && lowerI < startLeft + numLeft && startLeft + numLeft <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startLeft + numLeft - 1 - lowerI);
            //@
            //@ loop_invariant (\forall int i; lowerI < i && i < startLeft + numLeft - 1; indexL[i] == upper + (i - lowerI));
            //@
            //@ loop_invariant (\forall int i; begin <= i && i < begin + indexL[startLeft]; array[i] <= pivot);
            //@ loop_invariant (\forall int i; begin + upper < i && i <= last; pivot <= array[i]);
            //@
            //@ assignable lowerI, upper;
            //@ decreases lowerI + 1;
            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant 0 <= startLeft && startLeft - 1 <= lowerI && lowerI < startLeft + numLeft && startLeft + numLeft <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startLeft + numLeft - 1 - lowerI);
            //@ loop_invariant (\forall int i; startLeft <= i && i < lowerI; indexL[i] == indexL[i + 1] - 1);
            //@
            //@ loop_invariant (\forall int i; begin + indexL[startLeft] <= i && i < begin + upper; pivot <= array[i]);
            //@ loop_invariant (\forall int i; begin + upper < i && i <= last; pivot <= array[i]);
            //@
            //@ loop_invariant lowerI >= startLeft ==> indexL[lowerI] == upper || array[begin + upper] <= pivot; 
            //@ loop_invariant lowerI < startLeft && upper >= 0 ==> array[begin + upper] <= pivot;
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ loop_invariant (\forall int i; begin <= i && i < last + 1; (\num_of int k; begin <= k && k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k && k < last + 1; array[i] == \old(array[k])));
            //@
            //@ assignable upper, lowerI, array[begin + indexL[startLeft] .. last];
            //@ decreases lowerI + 1;
            while (lowerI >= startLeft) {
                swap(array, begin + upper, begin + indexL[lowerI]);
                upper--;
                lowerI--;
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            //@ loop_invariant 0 <= startRight && startRight - 1 <= lowerI && lowerI < startRight + numRight && startRight + numRight <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startRight + numRight - 1 - lowerI);
            //@ loop_invariant (\forall int i; lowerI < i && i < startRight + numRight - 1; indexR[i] == upper + (i - lowerI));
            //@
            //@ loop_invariant (\forall int i; last - indexR[startRight] < i && i <= last; pivot <= array[i]);
            //@ loop_invariant (\forall int i; begin <= i && i < last - upper; array[i] <= pivot);
            //@
            //@ assignable lowerI, upper;
            //@ decreases lowerI + 1;
            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant 0 <= startRight && startRight - 1 <= lowerI && lowerI < startRight + numRight && startRight + numRight <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startRight + numRight - 1 - lowerI);
            //@ loop_invariant (\forall int i; startRight <= i && i < lowerI; indexR[i] == indexR[i + 1] - 1);
            //@
            //@ loop_invariant (\forall int i; begin <= i && i < last - upper; array[i] <= pivot);
            //@ loop_invariant (\forall int i; last - upper < i && i <= last - indexR[startRight]; array[i] <= pivot);
            //@
            //@ loop_invariant lowerI >= startRight ==> indexR[lowerI] == upper || pivot <= array[last - upper];
            //@ loop_invariant lowerI < startRight && upper >= 0 ==> pivot <= array[last - upper];
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ loop_invariant (\forall int i; begin <= i && i < last + 1; (\num_of int k; begin <= k && k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k && k < last + 1; array[i] == \old(array[k])));
            //@
            //@ assignable upper, lowerI, array[begin .. last - indexR[startRight]];
            //@ decreases lowerI + 1;
            while (lowerI >= startRight) {
                swap(array, last - upper, last - indexR[lowerI]);
                upper--;
                lowerI--;
            }

            swap(array, pivotPosition, last - upper);
            return last - upper;
        } else {
            swap(array, pivotPosition, begin);
            return begin;
        }
    }

    // /*@
    //   @ public normal_behavior
    //   @ requires array != null;
    //   @ requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length;
    //   @ ensures array.length == \old(array.length);
    //   @
    //   @ // Values inside the range [originalBegin, originalEnd) are in sorted order.
    //   @ ensures (\forall int i; originalBegin <= i && i < originalEnd - 1; array[i] <= array[i+1]);
    //   @
    //   @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
    //   @ ensures permutation(array, \old(array), originalBegin, originalEnd);
    //   @
    //   @ assignable array[originalBegin .. originalEnd-1];
    //   @*/
    // public static void quickSort(int[] array, int originalBegin, int originalEnd) {
    //     int begin = originalBegin;
    //     int end = originalEnd;
    // 
    //     int depthLimit = 2 * log2(end - begin) + 3;
    //     int[] stack = new int[STACK_SIZE];
    //     int[] depthStack = new int[DEPTH_STACK_SIZE];
    //     int stackPointer = 0;
    //     int depthPointer = 0;
    //     int depth = 0;
    // 
    //     stack[stackPointer] = begin;
    //     stack[stackPointer + 1] = end;
    //     stackPointer += 2;
    //     depthStack[depthPointer] = depth;
    //     depthPointer++;
    // 
    //     /*@ loop_invariant 0 <= stackPointer && stackPointer < STACK_SIZE;
    //       @ loop_invariant 0 <= depth && depth <= depthLimit;
    //       @ loop_invariant originalBegin <= begin && begin <= end && end <= originalEnd;
    //       @
    //       @ // for (originalBegin, min(begin, min(stack[0 .. stackPointer]))) is ordered
    //       @ loop_invariant (\forall int i; originalBegin <= i && i < begin && (begin < (\min int j; 0 <= j && j < // stackPointer; stack[j]) ? begin : (\min int j; 0 <= j && j < stackPointer; stack[j]))); array[i] <= array[i+1]);
    //       @ 
    //       @ // for (max(end, max(stack[0 .. stackPointer])), originalEnd) is ordered
    //       @ loop_invariant (\forall int i; (end > (\max int j; 0 <= j && j < stackPointer; stack[j]) ? end : (\max int j; 0 // <= j && j < stackPointer; stack[j]))) <= i && i < originalEnd; array[i] <= array[i+1]);
    //       @
    //       @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
    //       @ loop_invariant (\forall int i; originalBegin <= i && i < originalEnd; (\num_of int k; originalBegin <= k && k < // originalEnd; array[i] == array[k]) == (\num_of int k; originalBegin <= k && k < originalEnd; array[i] == \old(array// [k])));
    //       @
    //       @ assignable stackPointer, depth, stack[0 .. STACK_SIZE - 1], array[originalBegin .. originalEnd - 1];
    //       @
    //       @ // outer loop decreases sum of num of elements out of order, aka sum (num of elements later than e which are // smaller than e)
    //       @ decreases (\sum int i; originalBegin <= i && i < originalEnd; (\num_of int j; i <= j && j < originalEnd; array[j] // < array[i]));
    //       @*/
    //     while (stackPointer > 0) {
    //         if (depth < depthLimit && (end - begin > IS_THRESH)) {
    //             int pivot = partition(array, begin, end);
    //             if (pivot - begin > end - pivot - 1) {
    //                 stack[stackPointer] = begin;
    //                 stack[stackPointer + 1] = pivot;
    //                 begin = pivot + 1;
    //             } else {
    //                 stack[stackPointer] = pivot + 1;
    //                 stack[stackPointer + 1] = end;
    //                 end = pivot;
    //             }
    //             stackPointer += 2;
    //             depth++;
    //             depthStack[depthPointer] = depth;
    //             depthPointer++;
    //         } else {
    //             insertionSort(array, begin, end);
    //             stackPointer -= 2;
    //             begin = stack[stackPointer];
    //             end = stack[stackPointer + 1];
    //             depthPointer--;
    //             depth = depthStack[depthPointer];
    //         }
    //     }
    // }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i && i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static void quickSortRec(int[] array, int begin, int end) {
        int depth = 0;
        int depthLimit = 2 * log2(end - begin) + 3;
        quickSortRecImpl(array, begin, end, depth, depthLimit);
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin <= end && end <= array.length;
      @ requires 0 <= depth && depth <= depthLimit && depthLimit < Integer.MAX_VALUE;
      @ ensures array.length == \old(array.length);
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i && i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static void quickSortRecImpl(int[] array, int begin, int end, int depth, int depthLimit) {

        if (end - begin <= IS_THRESH || depth >= depthLimit) {
            insertionSort(array, begin, end);
            return;
        }

        int pivot = partition(array, begin, end);
        quickSortRecImpl(array, begin, pivot, depth + 1, depthLimit);
        quickSortRecImpl(array, pivot, end, depth + 1, depthLimit);
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin <= end && end <= array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i && i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static void insertionSort(int[] array, int begin, int end) {
        for (int i = begin; i < end; i++) {
            int j = i;
            while (j > begin && array[j - 1] > array[j]) {
                swap(array, j, j - 1);
                j--;
            }
        }
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= i && i < array.length;
      @ requires 0 <= j && j < array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // Values at 'i' and 'j' are swapped.
      @ ensures array[i] == \old(array[j]) && array[j] == \old(array[i]);
      @
      @ assignable array[i], array[j];
      @*/
    public static void swap(int[] array, int i, int j) {
        int temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= i1 && i1 < array.length;
      @ requires 0 <= i2 && i2 < array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // Values at 'i1' and 'i2' are the old values but now sorted.
      @ ensures (\old(array[i1]) <= \old(array[i2])) 
      @         ? (array[i1] == \old(array[i1]) && array[i2] == \old(array[i2])) 
      @         : (array[i1] == \old(array[i2]) && array[i2] == \old(array[i1]));
      @
      @ assignable array[i1], array[i2];
      @*/
    public static void sortPair(int i1, int i2, int[] array) {
        if (array[i1] > array[i2]) {
            swap(array, i1, i2);
        }
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires end - begin >= 3;
      @ ensures array.length == \old(array.length);
      @
      @ // Result is within the given range [begin, end)
      @ ensures \result == begin + ((end - begin) / 2);
      @
      @ // Result is a valid median.
      @ ensures array[begin] <= array[\result] && array[\result] <= array[end - 1];
      @
      @ // The values at 'begin', 'end - 1', and 'begin + ((end - begin) / 2)' are a permutations of the values before. 
      @ ensures (\forall int i; begin <= i && i < end; (
      @                     (\num_of int j; begin <= j && j < end; array[i] == array[j]) ==
      @                     (\num_of int j; begin <= j && j < end; array[i] == \old(array[j]))
      @                    ));
      @
      @ assignable array[begin], array[begin + ((end - begin) / 2)], array[end - 1];
      @*/
    public static int medianOf3(int[] array, int begin, int end) {
        int mid = begin + ((end - begin) / 2);
        sortPair(begin, mid, array);
        sortPair(mid, end - 1, array);
        sortPair(begin, mid, array);
        return mid;
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires end - begin >= 3;
      @ ensures array.length == \old(array.length);
      @
      @ // The resulting pivot is inside the range [begin, end).
      @ ensures begin <= \result && \result < end;
      @
      @ // Values inside the range [begin, \result) are smaller than array[\result].
      @ ensures (\forall int i; begin <= i && i <= \result; array[i] <= array[\result]);
      @ // Values inside the range (\result, end) are greater than array[\result].
      @ ensures (\forall int i; \result <= i && i < end; array[\result] <= array[i]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static int partition(int[] array, int begin, int end) {
        int mid = medianOf3(array, begin, end);
        return hoareBlockPartition(array, begin + 1, end - 1, mid);
    }

    /*@ public normal_behavior
      @ requires n > 0;
      @ ensures 0 <= \result && (1 << (\result - 1)) < n && n <= (1 << \result) && \result <= 31;
      @ pure
      @*/
    public static int log2(int n) {
        int log2Value = 0;

        while (n > 1) {
            n /= 2;
            log2Value++;
        }

        return log2Value;
    }

    // /*@ public normal_behavior
    //   @ ensures \result == (a < b ? a : b);
    //   @ pure
    //   @*/
    public static int min(int a, int b) {
        return a < b ? a : b;
    }

    // /*@ public normal_behavior
    //   @ ensures \result == (a > b ? a : b);
    //   @ pure
    //   @*/
    public static int max(int a, int b) {
        return a > b ? a : b;
    }

    /*@
      @ public normal_behavior
      @ requires array1 != null;
      @ requires array2 != null;
      @ requires 0 <= begin && begin <= end && end <= array1.length;
      @ requires array1.length == array2.length;
      @ ensures array1.length == \old(array1.length);
      @ ensures array2.length == \old(array2.length);
      @ ensures \result == (\forall int i; begin <= i && i < end; (
      @                     (\num_of int j; begin <= j && j < end; array1[i] == array1[j]) ==
      @                     (\num_of int j; begin <= j && j < end; array1[i] == array2[j])
      @                    ));
      @ pure
      @*/
    public static boolean permutation(int[] array1, int[] array2, int begin, int end) {

        //@ loop_invariant begin <= i && i <= end;
        //@ loop_invariant (\forall int j; begin <= j && j < i; (\num_of int k; begin <= k && k < end; array1[j] == array1[k]) == (\num_of int k; begin <= k && k < end; array1[j] == array2[k]));
        //@ assignable i;
        //@ decreases end - i;
        for (int i = begin; i < end; i++) {
            int count1 = 0;
            int count2 = 0;

            //@ loop_invariant begin <= j && j <= end;
            //@ loop_invariant count1 == (\num_of int k; begin <= k && k < j; array1[i] == array1[k]);
            //@ loop_invariant count2 == (\num_of int k; begin <= k && k < j; array1[i] == array2[k]);
            //@ assignable j, count1, count2;
            //@ decreases end - j;
            for (int j = begin; j < end; j++) {
                if (array1[i] == array1[j]) {
                    count1++;
                }
                if (array1[i] == array2[j]) {
                    count2++;
                }
            }
            if (count1 != count2) {
                return false;
            }
        }
        return true;
    }
}
