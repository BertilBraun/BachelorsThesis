public class BlockQuickSort {

    private static final int BLOCKSIZE = 2; // \paper(128)
    private static final int IS_THRESH = 3; // \paper(16) must be a minimum of 3, since we use 3 elements for pivot selection
    private static final int STACK_SIZE = 10; // \paper(80)
    private static final int DEPTH_STACK_SIZE = 10; // \paper(40)

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length;
      @ requires originalBegin <= pivotPosition && pivotPosition < originalEnd;
      @
      @ // The resulting pivot is inside the range [originalBegin, originalEnd).
      @ ensures originalBegin <= \result && \result < originalEnd;
      @ ensures array[\result] == \old(array[pivotPosition]);
      @
      @ // Values inside the range [originalBegin, \result] are smaller or equal than array[\result].
      @ ensures (\forall int i; originalBegin <= i <= \result; array[i] <= array[\result]);
      @ // Values inside the range [\result, originalEnd) are greater or equal than array[\result].
      @ ensures (\forall int i; \result <= i < originalEnd; array[\result] <= array[i]);
      @
      @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
      @ // ensures permutation(array, \old(array), originalBegin, originalEnd);
      @ ensures (\forall int i; originalBegin <= i < originalEnd; (
      @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) ==
      @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j]))
      @         ));
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
              @ loop_invariant (\exists int i; 0 <= i < (originalEnd - originalBegin); begin == originalBegin + i * BLOCKSIZE);
              @ loop_invariant (\exists int i; 0 <= i < (originalEnd - originalBegin); last == originalEnd - 2 - i * BLOCKSIZE);
              @
              @ loop_invariant (\forall int i; 0 <= i < BLOCKSIZE; 0 <= indexL[i] && indexL[i] < BLOCKSIZE);
              @ loop_invariant (\forall int i; 0 <= i < numLeft; indexL[startLeft + i] < last - begin && pivot <= array[begin + indexL[startLeft + i]]);
              @ loop_invariant (\forall int i; 0 <= i < startLeft + numLeft - 1; indexL[i] < indexL[i + 1]);
              @ loop_invariant (numLeft != 0) ==> numLeft == (\num_of int i; startLeft <= i < BLOCKSIZE; pivot <= array[begin + i]);
              @
              @ loop_invariant (\forall int i; 0 <= i < BLOCKSIZE; 0 <= indexR[i] && indexR[i] < BLOCKSIZE);
              @ loop_invariant (\forall int i; 0 <= i < numRight; indexR[startRight + i] < last - begin && array[last - indexR[startRight + i]] <= pivot);
              @ loop_invariant (\forall int i; 0 <= i < startRight + numRight - 1; indexR[i] < indexR[i + 1]);
              @ loop_invariant (numRight != 0) ==> numRight == (\num_of int i; startRight <= i < BLOCKSIZE; array[last - i] <= pivot);
              @
              @ // The elements in the range [originalBegin, begin + indexL[startLeft]) are less than or equal pivot
              @ loop_invariant (numLeft == 0) ==> (\forall int i; originalBegin <= i < begin; array[i] <= pivot);
              @ loop_invariant (numLeft != 0) ==> (\forall int i; originalBegin <= i < begin + indexL[startLeft]; array[i] <= pivot);
              @
              @ // The elements in the range (last - indexR[startRight], originalEnd) are greater than or equal pivot 
              @ loop_invariant (numRight == 0) ==> (\forall int i; last < i < originalEnd; pivot <= array[i]);
              @ loop_invariant (numRight != 0) ==> (\forall int i; last - indexR[startRight] < i < originalEnd; pivot <= array[i]);
              @
              @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
              @ // loop_invariant permutation(array, \old(array), originalBegin, originalEnd);
              @ loop_invariant (\forall int i; originalBegin <= i < originalEnd; (
              @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) ==
              @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j]))
              @         ));
              @
              @ loop_modifies array[max(begin, originalBegin) .. min(begin + BLOCKSIZE - 1, originalEnd - 2)], 
              @               array[max(last - BLOCKSIZE - 1, originalBegin) .. min(last, originalEnd - 2)], 
              @               last, begin, numLeft, numRight, startLeft, startRight, num,
              @               indexL[0 .. min(array.length, BLOCKSIZE)-1], 
              @               indexR[0 .. min(array.length, BLOCKSIZE)-1];
              @
              @ loop_decreases last - begin;
              @*/
            while (last - begin + 1 > 2 * BLOCKSIZE) {

                if (numLeft == 0) {
                    startLeft = 0;

                    //@ loop_invariant 0 <= j <= BLOCKSIZE;
                    //@ // Maintain numLeft count
                    //@ loop_invariant numLeft == (\num_of int k; 0 <= k < j; pivot <= array[begin + k]);
                    //@ // Maintain indexL array
                    //@ loop_invariant (\forall int k; 0 <= k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
                    //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
                    //@ // Maintain sorted indexL
                    //@ loop_invariant (\forall int k; 0 <= k < numLeft - 1; indexL[k] < indexL[k + 1]);
                    //@
                    //@ loop_modifies numLeft, indexL[0 .. min(array.length, BLOCKSIZE)-1], j;
                    //@ loop_decreases BLOCKSIZE - j;
                    for (int j = 0; j < BLOCKSIZE; j++) {
                        indexL[numLeft] = j;
                        numLeft += array[begin + j] >= pivot ? 1 : 0;
                    }
                }
                if (numRight == 0) {
                    startRight = 0;
                    //@ loop_invariant 0 <= j <= BLOCKSIZE;
                    //@ // Maintain numRight count
                    //@ loop_invariant numRight == (\num_of int k; 0 <= k < j; array[last - k] <= pivot);
                    //@ // Maintain indexR array
                    //@ loop_invariant (\forall int k; 0 <= k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
                    //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
                    //@ // Maintain sorted indexR
                    //@ loop_invariant (\forall int k; 0 <= k < numRight - 1; indexR[k] < indexR[k + 1]);
                    //@
                    //@ loop_modifies numRight, indexR[0 .. min(array.length, BLOCKSIZE)-1], j;
                    //@ loop_decreases BLOCKSIZE - j;
                    for (int j = 0; j < BLOCKSIZE; j++) {
                        indexR[numRight] = j;
                        numRight += pivot >= array[last - j] ? 1 : 0;
                    }
                }

                num = min(numLeft, numRight);
                if (num > 0) {
                    //@ loop_invariant 0 <= j <= num;
                    //@ 
                    //@ // Values inside the range [originalBegin, begin + indexL[startLeft + j]) are less than or equal to pivot.
                    //@ loop_invariant (\forall int i; originalBegin <= i < begin + indexL[startLeft]; array[i] <= pivot);
                    //@ loop_invariant j > 0 ==> (\forall int i; originalBegin <= i <= begin + indexL[startLeft + j - 1]; array[i] <= pivot);
                    //@
                    //@ // Values inside the range (last - indexR[startRight - j], originalEnd) are greater than or equal to pivot.
                    //@ loop_invariant (\forall int i; last - indexR[startRight] < i < originalEnd; pivot <= array[i]);
                    //@ loop_invariant j > 0 ==> (\forall int i; last - indexR[startRight + j - 1] <= i < originalEnd; pivot <= array[i]);
                    //@
                    //@ // All values indexed by indexL[startLeft + j .. startLeft + numLeft] are greater than or equal to pivot.
                    //@ loop_invariant (\forall int i; startLeft + j <= i < startLeft + numLeft; pivot <= array[begin + indexL[i]]);
                    //@
                    //@ // All values indexed by indexR[startRight + j .. startRight + numRight] are less than or equal to pivot.
                    //@ loop_invariant (\forall int i; startRight + j <= i < startRight + numRight; array[last - indexR[i]] <= pivot);
                    //@
                    //@ // Values inside the range [begin, last] are a valid permutation.
                    //@ // loop_invariant permutation(array, \old(array), begin, last + 1);
                    //@ loop_invariant (\forall int i; begin <= i < last + 1; ((\num_of int k; begin <= k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k < last + 1; array[i] == \old(array[k]))));
                    //@
                    //@ loop_modifies array[begin + indexL[startLeft] .. begin + indexL[startLeft + num - 1]], array[last - indexR[startRight + num - 1] .. last - indexR[startRight]], j;
                    //@ loop_decreases num - j;
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
            //@ loop_invariant 0 <= j <= shiftL;
            //@ loop_invariant 0 <= numLeft && numLeft <= j;
            //@ loop_invariant 0 <= numRight && numRight <= j;
            //@
            //@ // Maintain numLeft count
            //@ loop_invariant numLeft == (\num_of int k; 0 <= k < j; pivot <= array[begin + k]);
            //@ // Maintain numRight count
            //@ loop_invariant numRight == (\num_of int k; 0 <= k < j; array[last - k] <= pivot);
            //@
            //@ // Maintain indexL array
            //@ loop_invariant (\forall int k; 0 <= k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
            //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
            //@ // Maintain indexR array
            //@ loop_invariant (\forall int k; 0 <= k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
            //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
            //@
            //@ // Maintain sorted indexL
            //@ loop_invariant (\forall int k; 0 <= k < numLeft - 1; indexL[k] < indexL[k + 1]);
            //@ // Maintain sorted indexR
            //@ loop_invariant (\forall int k; 0 <= k < numRight - 1; indexR[k] < indexR[k + 1]);
            //@
            //@ loop_decreases shiftL - j;
            //@ loop_modifies indexL[0 .. shiftL - 1], numLeft, indexR[0 .. shiftL - 1], numRight, j;
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
            //@ loop_invariant 0 <= j <= shiftL;
            //@ // Maintain numLeft count
            //@ loop_invariant numLeft == (\num_of int k; 0 <= k < j; pivot <= array[begin + k]);
            //@ // Maintain indexL array
            //@ loop_invariant (\forall int k; 0 <= k < numLeft; 0 <= indexL[k] && indexL[k] < j && pivot <= array[begin + indexL[k]]);
            //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexL[k] && indexL[k] < BLOCKSIZE);
            //@ // Maintain sorted indexL
            //@ loop_invariant (\forall int k; 0 <= k < numLeft - 1; indexL[k] < indexL[k + 1]);
            //@
            //@ loop_modifies numLeft, indexL[0 .. shiftL-1], j;
            //@ loop_decreases shiftL - j;
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;
            //@ loop_invariant 0 <= j <= shiftR;
            //@ // Maintain numRight count
            //@ loop_invariant numRight == (\num_of int k; 0 <= k < j; array[last - k] <= pivot);
            //@ // Maintain indexR array
            //@ loop_invariant (\forall int k; 0 <= k < numRight; 0 <= indexR[k] && indexR[k] < j && array[last - indexR[k]] <= pivot);
            //@ loop_invariant (\forall int k; 0 <= k < BLOCKSIZE; 0 <= indexR[k] && indexR[k] < BLOCKSIZE);
            //@ // Maintain sorted indexR
            //@ loop_invariant (\forall int k; 0 <= k < numRight - 1; indexR[k] < indexR[k + 1]);
            //@
            //@ loop_modifies numRight, indexR[0 .. shiftR-1], j;
            //@ loop_decreases shiftR - j;
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
        }

        num = min(numLeft, numRight);
        if (num > 0) {
            //@ loop_invariant 0 <= j <= num;
            //@ 
            //@ // Values inside the range [originalBegin, begin + indexL[startLeft + j]) are less than or equal to pivot.
            //@ loop_invariant (\forall int i; originalBegin <= i < begin + indexL[startLeft]; array[i] <= pivot);
            //@ loop_invariant j > 0 ==> (\forall int i; originalBegin <= i <= begin + indexL[startLeft + j - 1]; array[i] <= pivot);
            //@
            //@ // Values inside the range (last - indexR[startRight - j], originalEnd) are greater than or equal to pivot.
            //@ loop_invariant (\forall int i; last - indexR[startRight] < i < originalEnd; pivot <= array[i]);
            //@ loop_invariant j > 0 ==> (\forall int i; last - indexR[startRight + j - 1] <= i < originalEnd; pivot <= array[i]);
            //@
            //@ // All values indexed by indexL[startLeft + j .. startLeft + numLeft] are greater than or equal to pivot.
            //@ loop_invariant (\forall int i; startLeft + j <= i < startLeft + numLeft; pivot <= array[begin + indexL[i]]);
            //@
            //@ // All values indexed by indexR[startRight + j .. startRight + numRight] are less than or equal to pivot.
            //@ loop_invariant (\forall int i; startRight + j <= i < startRight + numRight; array[last - indexR[i]] <= pivot);
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ // loop_invariant permutation(array, \old(array), begin, last + 1);
            //@ loop_invariant (\forall int i; begin <= i < last + 1; ((\num_of int k; begin <= k < last + 1; array[i] == array[k]) == (\num_of int k; begin <= k < last + 1; array[i] == \old(array[k]))));
            //@
            //@ loop_modifies array[begin + indexL[startLeft] .. begin + indexL[startLeft + num - 1]], array[last - indexR[startRight + num - 1] .. last - indexR[startRight]], j;
            //@ loop_decreases num - j;
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
            //@ loop_invariant (\forall int i; lowerI < i < startLeft + numLeft - 1; indexL[i] == upper + (i - lowerI));
            //@
            //@ loop_invariant (\forall int i; begin <= i < begin + indexL[startLeft]; array[i] <= pivot);
            //@ loop_invariant (\forall int i; begin + upper < i <= last; pivot <= array[i]);
            //@
            //@ loop_modifies lowerI, upper;
            //@ loop_decreases lowerI + 1;
            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant 0 <= startLeft && startLeft - 1 <= lowerI && lowerI < startLeft + numLeft && startLeft + numLeft <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startLeft + numLeft - 1 - lowerI);
            //@ loop_invariant (\forall int i; startLeft <= i < lowerI; indexL[i] == indexL[i + 1] - 1);
            //@
            //@ loop_invariant (\forall int i; begin + indexL[startLeft] <= i < begin + upper; pivot <= array[i]);
            //@ loop_invariant (\forall int i; begin + upper < i <= last; pivot <= array[i]);
            //@
            //@ loop_invariant lowerI >= startLeft ==> indexL[lowerI] == upper || array[begin + upper] <= pivot; 
            //@ loop_invariant lowerI < startLeft && upper >= 0 ==> array[begin + upper] <= pivot;
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ // loop_invariant permutation(array, \old(array), begin, last + 1);
            //@ loop_invariant (\forall int i; begin <= i < last + 1; ((\num_of int j; begin <= j < last + 1; array[i] == array[j]) == (\num_of int j; begin <= j < last + 1; array[i] == \old(array[j]))));
            //@
            //@ loop_modifies upper, lowerI, array[begin + indexL[startLeft] .. last];
            //@ loop_decreases lowerI + 1;
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
            //@ loop_invariant (\forall int i; lowerI < i < startRight + numRight - 1; indexR[i] == upper + (i - lowerI));
            //@
            //@ loop_invariant (\forall int i; last - indexR[startRight] < i <= last; pivot <= array[i]);
            //@ loop_invariant (\forall int i; begin <= i < last - upper; array[i] <= pivot);
            //@
            //@ loop_modifies lowerI, upper;
            //@ loop_decreases lowerI + 1;
            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant 0 <= startRight && startRight - 1 <= lowerI && lowerI < startRight + numRight && startRight + numRight <= BLOCKSIZE;
            //@ loop_invariant upper == last - begin - (startRight + numRight - 1 - lowerI);
            //@ loop_invariant (\forall int i; startRight <= i < lowerI; indexR[i] == indexR[i + 1] - 1);
            //@
            //@ loop_invariant (\forall int i; begin <= i < last - upper; array[i] <= pivot);
            //@ loop_invariant (\forall int i; last - upper < i <= last - indexR[startRight]; array[i] <= pivot);
            //@
            //@ loop_invariant lowerI >= startRight ==> indexR[lowerI] == upper || pivot <= array[last - upper];
            //@ loop_invariant lowerI < startRight && upper >= 0 ==> pivot <= array[last - upper];
            //@
            //@ // Values inside the range [begin, last] are a valid permutation.
            //@ // loop_invariant permutation(array, \old(array), begin, last + 1);
            //@ loop_invariant (\forall int i; begin <= i < last + 1; ((\num_of int j; begin <= j < last + 1; array[i] == array[j]) == (\num_of int j; begin <= j < last + 1; array[i] == \old(array[j]))));
            //@
            //@ loop_modifies upper, lowerI, array[begin .. last - indexR[startRight]];
            //@ loop_decreases lowerI + 1;
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

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length;
      @
      @ // Values inside the range [originalBegin, originalEnd) are in sorted order.
      @ ensures (\forall int i; originalBegin <= i < originalEnd - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
      @ // ensures permutation(array, \old(array), originalBegin, originalEnd);
      @ ensures (\forall int i; originalBegin <= i < originalEnd; (
      @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) ==
      @          (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j]))
      @         ));
      @
      @ assignable array[originalBegin .. originalEnd-1];
      @*/
    public static void quickSort(int[] array, int originalBegin, int originalEnd) {
        int begin = originalBegin;
        int end = originalEnd;

        int depthLimit = 2 * log2(end - begin) + 3;
        int[] stack = new int[STACK_SIZE];
        int[] depthStack = new int[DEPTH_STACK_SIZE];
        int stackPointer = 0;
        int depthPointer = 0;
        int depth = 0;

        stack[stackPointer] = begin;
        stack[stackPointer + 1] = end;
        stackPointer += 2;
        depthStack[depthPointer] = depth;
        depthPointer++;

        /*@ loop_invariant 0 <= stackPointer && stackPointer % 2 == 0 && stackPointer <= STACK_SIZE;
          @ loop_invariant 0 <= depthPointer && depthPointer == stackPointer / 2;
          @ loop_invariant 0 <= depth && depth <= depthLimit;
          @ loop_invariant originalBegin <= begin && begin < end && end <= originalEnd;
          @
          @ loop_invariant (\sum int i; 1 <= i < stackPointer / 2; stack[2*i+1] - stack[2*i]) <= originalEnd - originalBegin;
          @ loop_invariant (\forall int i; 0 <= i < stackPointer / 2; originalBegin <= stack[2*i] && stack[2*i] < stack[2*i+1] && stack[2*i+1] <= originalEnd);
          @ loop_invariant stack[0] == originalBegin && stack[1] == originalEnd;
          @ loop_invariant (\forall int i; 0 <= i < depthPointer; 0 <= depthStack[i] && depthStack[i] <= depthLimit);
          @
          @ // stack is non overlapping i.e. no two ranges on the stack overlap and also begin and end are not inside any range on the stack
          @ loop_invariant (\forall int i; 1 <= i < stackPointer / 2; 
          @                 (\forall int j; 1 <= j < stackPointer / 2; i == j || stack[2*i+1] <= stack[2*j] || stack[2*j+1] <= stack[2*i]) && 
          @                 (stack[2*i+1] <= begin || end <= stack[2*i])
          @                );
          @
          @ // all elements not pointed to by a range on the stack are already in sorted order
          @ // For all indices, all elements to the left are smaller and all elements to the right are bigger than it (or equal) if they are not pointed to by a range on the stack
          @ loop_invariant (\forall int i; originalBegin <= i < originalEnd; (
          @                 ((\exists int j; 1 <= j < stackPointer / 2; stack[2*j] <= i < stack[2*j+1])) || (stackPointer != 0 && begin <= i < end) || (
          @                  (\forall int j; originalBegin <= j < i; array[j] <= array[i]) &&
          @                  (\forall int j; i < j < originalEnd; array[i] <= array[j])
          @                 )
          @                ));
          @
          @ // for each range on the stack:
          @ // - there does not exist and elements to the left of the minimum Index indicated by the range that is greater than the Minimum Element pointed to by any element of that range
          @ // - there does not exist and elements to the right of the maximum Index indicated by the range that is smaller than the Maximum Element pointed to by any element of that range
          @ loop_invariant (\forall int i; 1 <= i < stackPointer / 2; (
          @                 (\forall int j; originalBegin <= j < stack[2*i]; 
          @                   array[j] <= (\min int k; stack[2*i] <= k < stack[2*i+1]; array[k])
          @                 ) &&
          @                 (\forall int j; stack[2*i+1] <= j < originalEnd;
          @                   (\max int k; stack[2*i] <= k < stack[2*i+1]; array[k]) <= array[j]
          @                 )
          @                ));
          @
          @ // Values inside the range [originalBegin, originalEnd) are a valid permutation.
          @ // loop_invariant permutation(array, \old(array), originalBegin, originalEnd);
          @ loop_invariant (\forall int i; originalBegin <= i < originalEnd; (
          @                 (\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) ==
          @                 (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j]))
          @                ));
          @
          @ loop_modifies stackPointer, begin, end, depth, depthPointer,
          @               array[originalBegin .. originalEnd-1],  
          @               depthStack[0 .. min(array.length, DEPTH_STACK_SIZE)-1], 
          @               stack[0 .. min(array.length, STACK_SIZE)-1]; 
          @
          @ // the loop decreases the number of elements out of order (aka still on the stack)
          @ // in the upper case, by one (the pivot), in the lower case by (end - begin) (which is at least one because of the added special case)
          @ loop_decreases (\sum int i; 0 <= i < stackPointer / 2; stack[2*i+1] - stack[2*i]) + (end - begin + 1);       
          @*/
        while (stackPointer > 0) {
            // Added stackPointer < STACK_SIZE - should not be necessary, should be caught by depth < depthLimit
            if (depth < depthLimit && (end - begin > IS_THRESH) && stackPointer < STACK_SIZE) {
                int pivot = partition(array, begin, end);
                if (pivot - begin > end - pivot) {
                    // Added special case that empty ranges are not pushed on the stack - only adds one iteration more
                    if (end - (pivot + 1) <= 0) {
                        end = pivot;
                    } else {
                        stack[stackPointer] = begin;
                        stack[stackPointer + 1] = pivot;
                        stackPointer += 2;
                        begin = pivot + 1;
                        depth++;
                        depthStack[depthPointer] = depth;
                        depthPointer++;
                    }
                } else {
                    // Added special case that empty ranges are not pushed on the stack - only adds one iteration more
                    if (pivot - begin <= 0) {
                        begin = pivot + 1;
                    } else {
                        stack[stackPointer] = pivot + 1;
                        stack[stackPointer + 1] = end;
                        stackPointer += 2;
                        end = pivot;
                        depth++;
                        depthStack[depthPointer] = depth;
                        depthPointer++;
                    }
                }
            } else {
                insertionSort(array, begin, end);
                stackPointer -= 2;
                begin = stack[stackPointer];
                end = stack[stackPointer + 1];
                depthPointer--;
                depth = depthStack[depthPointer];
            }
        }
    }

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin < end && end <= array.length;
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ // ensures permutation(array, \old(array), begin, end);
      @ ensures (\forall int i; begin <= i < end; (
      @          (\num_of int j; begin <= j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j < end; array[i] == \old(array[j]))
      @         ));
      @
      @ assignable array[begin .. end-1];
      @*/
    public static void quickSortRec(int[] array, int begin, int end) {
        int depth = 0;
        int depthLimit = 2 * log2(end - begin) + 3;
        quickSortRecImpl(array, begin, end, depth, depthLimit);
    }

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin <= end && end <= array.length;
      @ requires 0 <= depth && depth <= depthLimit && depthLimit < Integer.MAX_VALUE;
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ // ensures permutation(array, \old(array), begin, end);
      @ ensures (\forall int i; begin <= i < end; (
      @          (\num_of int j; begin <= j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j < end; array[i] == \old(array[j]))
      @         ));
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

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin <= end && end <= array.length;
      @
      @ // Values inside the range [begin, end) are in sorted order.
      @ ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i+1]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ // ensures permutation(array, \old(array), begin, end);
      @ ensures (\forall int i; begin <= i < end; (
      @          (\num_of int j; begin <= j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j < end; array[i] == \old(array[j]))
      @         ));
      @
      @ assignable array[begin .. end-1];
      @*/
    public static void insertionSort(int[] array, int begin, int end) {
        //@ loop_invariant begin <= i && i <= end;
        //@ loop_invariant (\forall int j; begin <= j < i - 1; array[j] <= array[j+1]);
        //@ // loop_invariant permutation(array, \old(array), begin, end);
        //@ loop_invariant (\forall int l; begin <= l < end; ((\num_of int j; begin <= j < end; array[l] == array[j]) == (\num_of int j; begin <= j < end; array[l] == \old(array[j]))));
        //@ loop_modifies array[begin .. end-1], i; 
        //@ loop_decreases end - i;
        for (int i = begin; i < end; i++) {
            //@ loop_invariant begin <= j && j <= i;
            //@ loop_invariant (\forall int k; begin <= k < j - 1; array[k] <= array[k+1]);
            //@ loop_invariant (\forall int k; j < k <= i; (\forall int l; begin <= l <= k; array[k] >= array[l]));
            //@ // loop_invariant permutation(array, \old(array), begin, end);
            //@ loop_invariant (\forall int l; begin <= l < end; ((\num_of int k; begin <= k < end; array[l] == array[k]) == (\num_of int k; begin <= k < end; array[l] == \old(array[k]))));
            //@ loop_modifies array[begin .. i], j;
            //@ loop_decreases j;
            for (int j = i; j > begin && array[j - 1] > array[j]; j--) {
                swap(array, j, j - 1);
            }
        }
    }

    /*@ public normal_behavior
      @ requires array != null;
      @ requires 0 <= i < array.length;
      @ requires 0 <= j < array.length;
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

    /*@ public normal_behavior
      @ requires array != null;
      @ requires 0 <= i1 && i1 < array.length;
      @ requires 0 <= i2 && i2 < array.length;
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

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires end - begin >= 3;
      @
      @ // Result is within the given range [begin, end)
      @ ensures \result == begin + ((end - begin) / 2);
      @
      @ // Result is a valid median.
      @ ensures array[begin] <= array[\result] && array[\result] <= array[end - 1];
      @
      @ // The values at 'begin', 'end - 1', and 'begin + ((end - begin) / 2)' are a permutations of the values before. 
      @ // ensures permutation(array, \old(array), begin, end);
      @ ensures (\forall int i; begin <= i < end; (
      @          (\num_of int j; begin <= j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j < end; array[i] == \old(array[j]))
      @         ));
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

    /*@ public normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; 0 <= array[i] < array.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires end - begin >= 3;
      @
      @ // The resulting pivot is inside the range [begin, end).
      @ ensures begin <= \result && \result < end;
      @
      @ // Values inside the range [begin, \result) are smaller than array[\result].
      @ ensures (\forall int i; begin <= i <= \result; array[i] <= array[\result]);
      @ // Values inside the range (\result, end) are greater than array[\result].
      @ ensures (\forall int i; \result <= i < end; array[\result] <= array[i]);
      @
      @ // Values inside the range [begin, end) are a valid permutation. 
      @ // ensures permutation(array, \old(array), begin, end);
      @ ensures (\forall int i; begin <= i < end; (
      @          (\num_of int j; begin <= j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j < end; array[i] == \old(array[j]))
      @         ));
      @
      @ assignable array[begin .. end-1];
      @*/
    public static int partition(int[] array, int begin, int end) {
        int mid = medianOf3(array, begin, end);
        return hoareBlockPartition(array, begin + 1, end - 1, mid);
    }

    /*@ public normal_behavior
      @ requires 0 < originalN;
      @ ensures 0 <= \result && (1 << \result) <= originalN && originalN <= (1 << (\result + 1)) && \result <= 31;
      @ pure
      @*/
    public static int log2(int originalN) {
        int log2Value = 0;
        int n = originalN;

        while (n > 1) {
            n /= 2;
            log2Value++;
        }

        return log2Value;
    }

    // Does not work with \old() yet.
    // /*@ public normal_behavior
    //   @ ensures \result == (a < b ? a : b);
    //   @ pure
    //   @*/
    public static int min(int a, int b) {
        return a < b ? a : b;
    }

    // Does not work with \old() yet.
    // /*@ public normal_behavior
    //   @ ensures \result == (a > b ? a : b);
    //   @ pure
    //   @*/
    public static int max(int a, int b) {
        return a > b ? a : b;
    }

    /*@ public normal_behavior
      @ requires array1 != null;
      @ requires array2 != null;
      @ requires (\forall int i; 0 <= i < array1.length; 0 <= array1[i] < array1.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires (\forall int i; 0 <= i < array2.length; 0 <= array2[i] < array2.length); // NOTE: Does not change the verification results, but speeds up the verification a lot.
      @ requires 0 <= begin && begin <= end && end <= array1.length;
      @ requires array1.length == array2.length;
      @ ensures array1.length == \old(array1.length);
      @ ensures array2.length == \old(array2.length);
      @ ensures \result == (\forall int i; begin <= i < end; (
      @                     (\num_of int j; begin <= j < end; array1[i] == array1[j]) ==
      @                     (\num_of int j; begin <= j < end; array1[i] == array2[j])
      @                    ));
      @ pure
      @*/
    public static boolean permutation(int[] array1, int[] array2, int begin, int end) {

        //@ loop_invariant begin <= i <= end;
        //@ loop_invariant (\forall int j; begin <= j < i; (\num_of int k; begin <= k < end; array1[j] == array1[k]) == (\num_of int k; begin <= k < end; array1[j] == array2[k]));
        //@ loop_modifies i;
        //@ loop_decreases end - i;
        for (int i = begin; i < end; i++) {
            int count1 = 0;
            int count2 = 0;

            //@ loop_invariant begin <= j <= end;
            //@ loop_invariant count1 == (\num_of int k; begin <= k < j; array1[i] == array1[k]);
            //@ loop_invariant count2 == (\num_of int k; begin <= k < j; array1[i] == array2[k]);
            //@ loop_modifies j, count1, count2;
            //@ loop_decreases end - j;
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
