
import java.util.Arrays;

public class BlockQuickSort {

    private static final int BLOCKSIZE = 2; // 128
    private static final int IS_THRESH = 2; // 16
    private static final int STACK_SIZE = 80;

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires begin <= pivotPosition && pivotPosition < end;
      @ ensures array.length == \old(array.length);
      @
      @ // The resulting pivot is inside the range [begin, end).
      @ ensures begin <= \result && \result < end;
      @
      @ // Values inside the range [begin, \result) are smaller than array[\result].
      @ ensures (\forall int i; begin <= i && i < \result; array[i] <= array[\result]);
      @ // Values inside the range (\result, end) are greater than array[\result].
      @ ensures (\forall int i; \result < i && i < end; array[\result] <= array[i]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static int hoareBlockPartition(
            int[] array,
            int begin,
            int end,
            int pivotPosition) {
        int[] indexL = new int[BLOCKSIZE];
        int[] indexR = new int[BLOCKSIZE];

        int last = end - 1;
        int pivot = array[pivotPosition];
        swap(array, pivotPosition, last);
        pivotPosition = last;
        last--;

        int numLeft = 0;
        int numRight = 0;
        int startLeft = 0;
        int startRight = 0;
        int num;

        /* TODO */
        while (last - begin + 1 > 2 * BLOCKSIZE) {
            if (numLeft == 0) {
                startLeft = 0;
                /*@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                  @ // Maintain numLeft count
                  @ loop_invariant numLeft == (\num_of int k; 0 <= k && k < j; array[begin + k] >= pivot);
                  @ // Maintain indexL array
                  @ loop_invariant (\forall int k; 0 <= k && k < numLeft; 0 <= indexL[k] && indexL[k] < j && array[begin + indexL[k]] >= pivot);
                  @
                  @ loop_modifies numLeft, indexL[*], j;
                  @ loop_decreases BLOCKSIZE - j;
                  @*/
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexL[numLeft] = j;
                    numLeft += array[begin + j] >= pivot ? 1 : 0;
                }
            }
            if (numRight == 0) {
                startRight = 0;
                /*@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                  @ // Maintain numRight count
                  @ loop_invariant numRight == (\num_of int k; 0 <= k && k < j; pivot >= array[last - k]);
                  @ // Maintain indexR array
                  @ loop_invariant (\forall int k; 0 <= k && k < numRight; 0 <= indexR[k] && indexR[k] < j && pivot >= array[last - indexR[k]]);
                  @
                  @ loop_modifies numRight, indexR[*], j;
                  @ loop_decreases BLOCKSIZE - j;
                  @*/
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexR[numRight] = j;
                    numRight += pivot >= array[last - j] ? 1 : 0;
                }
            }

            num = Math.min(numLeft, numRight);
            /*@ loop_invariant 0 <= j && j <= num;
              @ // The elements in the range [begin, begin + indexL[startLeft]) and [last - indexR[startRight], last] remain unchanged
              @ loop_invariant (\forall int i; 0 <= i && i < startLeft; array[begin + indexL[i]] == \old(array[begin + indexL[i]])) &&
              @                 (\forall int i; 0 <= i && i < startRight; array[last - indexR[i]] == \old(array[last - indexR[i]]));
              @ // The elements in the range [begin + indexL[startLeft + j], begin + indexL[startLeft + num]) and [last - indexR[startRight + num], last - indexR[startRight + j]) are rearranged such that elements smaller than the pivot are moved to the left of the pivot and elements greater than the pivot are moved to the right of the pivot
              @ loop_invariant (\forall int i; startLeft <= i && i < startLeft + j; array[begin + indexL[i]] <= pivot) &&
              @                 (\forall int i; startRight <= i && i < startRight + j; array[last - indexR[i]] >= pivot);
              @ loop_modifies array[*], j;
              @*/
            for (int j = 0; j < num; j++) {
                swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
            }

            numLeft -= num;
            numRight -= num;
            startLeft += num;
            startRight += num;
            begin += (numLeft == 0) ? BLOCKSIZE : 0;
            last -= (numRight == 0) ? BLOCKSIZE : 0;
        }

        int shiftR = 0, shiftL = 0;
        if (numRight == 0 && numLeft == 0) {
            shiftL = ((last - begin) + 1) / 2;
            shiftR = (last - begin) + 1 - shiftL;
            startLeft = 0;
            startRight = 0;
            /*@ loop_invariant 0 <= j && j <= shiftL;
              @ loop_invariant 0 <= numLeft && numLeft <= j;
              @ loop_invariant 0 <= numRight && numRight <= j;
              @
              @ loop_invariant (\forall int k; 0 <= k && k < numLeft; array[begin + indexL[k]] >= pivot);
              @ loop_invariant (\forall int k; 0 <= k && k < numRight; pivot >= array[last - indexR[k]]);
              @
              @ loop_decreases shiftL - j;
              @ loop_modifies indexL[*], numLeft, indexR[*], numRight, j;
              @*/
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
            /*@ loop_invariant 0 <= j && j <= shiftL;
              @ // The number of elements >= pivot is always <= j
              @ loop_invariant 0 <= numLeft && numLeft <= j;
              @ // All stored indices are in the range [0, shiftL)
              @ loop_invariant (\forall int i; 0 <= i && i < numLeft; indexL[i] >= 0 && indexL[i] < shiftL);
              @ // All elements in indexL are >= pivot
              @ loop_invariant (\forall int i; 0 <= i && i < numLeft; array[begin + indexL[i]] >= pivot);
              @ loop_modifies indexL[*], numLeft, j;
              @ loop_decreases shiftL - j;
              @*/
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;
            /*@ loop_invariant 0 <= j && j <= shiftR;
              @ loop_invariant 0 <= numRight && numRight <= j;
              @ loop_invariant (\forall int i; 0 <= i && i < numRight; last - indexR[i] >= begin && last - indexR[i] <= last);
              @ loop_invariant (\forall int i; 0 <= i && i < numRight; array[last - indexR[i]] <= pivot);
              @ loop_modifies numRight, indexR[*], j;
              @ loop_decreases shiftR - j;
              @*/
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
        }

        num = Math.min(numLeft, numRight);
        /*@ loop_invariant 0 <= j && j <= num;
          @ // Ensures that 'j' remains within the valid range
          @
          @ loop_invariant startLeft <= startLeft + j && startLeft + j < startLeft + numLeft;
          @ // Ensures that 'startLeft + j' stays within the valid range for indexL
          @
          @ loop_invariant startRight <= startRight + j && startRight + j < startRight + numRight;
          @ // Ensures that 'startRight + j' stays within the valid range for indexR
          @
          @ loop_invariant (\forall int i; 0 <= i && i < j; array[begin + indexL[startLeft + i]] <= array[last - indexR[startRight + i]]);
          @ // Ensures that the loop maintains the desired property (elements smaller than the pivot on the left, elements greater than the pivot on the right) for the current indices in indexL and indexR
          @
          @ loop_modifies array[*], indexL[*], indexR[*];
          @ loop_decreases num - j;
          @*/
        for (int j = 0; j < num; j++) {
            swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
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

            //@ loop_invariant lowerI >= startLeft - 1 && lowerI < numLeft;
            //@ loop_invariant upper >= -1 && upper < last - begin;
            //@ loop_invariant (lowerI == startLeft - 1) || (indexL[lowerI] == upper);
            //@ loop_modifies upper, lowerI;
            //@ loop_decreases startLeft + 1 - lowerI;
            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant lowerI >= startLeft - 1 && lowerI < numLeft;
            //@ loop_invariant upper >= -1 && upper < last - begin;
            //@ loop_invariant (\forall int i; 0 <= i && i < startLeft; array[begin + indexL[i]] < pivot);
            //@ loop_invariant (\forall int i; startLeft <= i && i < lowerI + 1; array[begin + indexL[i]] >= pivot);
            //@ loop_modifies array[begin .. last], upper, lowerI;
            //@ loop_decreases startLeft + 1 - lowerI;
            while (lowerI >= startLeft) {
                swap(array, begin + upper--, begin + indexL[lowerI--]);
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            //@ loop_invariant lowerI >= startRight - 1 && lowerI < numLeft;
            //@ loop_invariant upper >= -1 && upper < last - begin;
            //@ loop_invariant (lowerI == startRight - 1) || (indexL[lowerI] == upper);
            //@ loop_modifies upper, lowerI;
            //@ loop_decreases startRight + 1 - lowerI;
            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant lowerI >= startRight - 1 && lowerI < numLeft;
            //@ loop_invariant upper >= -1 && upper < last - begin;
            //@ loop_invariant (\forall int i; 0 <= i && i < startRight; array[begin + indexL[i]] < pivot);
            //@ loop_invariant (\forall int i; startRight <= i && i < lowerI + 1; array[begin + indexL[i]] >= pivot);
            //@ loop_modifies array[begin .. last], upper, lowerI;
            //@ loop_decreases startRight + 1 - lowerI;
            while (lowerI >= startRight) {
                swap(array, last - upper--, last - indexR[lowerI--]);
            }

            swap(array, pivotPosition, last - upper);
            return last - upper;
        } else {
            swap(array, pivotPosition, begin);
            return begin;
        }
    }

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
    public static void quickSort(int[] array, int begin, int end) {
        int[] stack = new int[STACK_SIZE];
        int top = 0;
        int depth = 0;
        int depthLimit = (int) (2 * Math.log(end - begin) / Math.log(2)) + 3;

        stack[top++] = begin;
        stack[top++] = end;

        /*@ loop_invariant
          @   // Stack-related invariants:
          @   stack != null && stack.length == STACK_SIZE &&
          @   top % 2 == 0 && 0 <= top && top <= STACK_SIZE &&
          @   (\forall int i; 0 <= i && i < top; 0 <= stack[i] && stack[i] < array.length) &&
          @   (\forall int i; 0 <= i && i < top - 1; i % 2 == 0 ==> stack[i] < stack[i+1]) &&
          @
          @   // Subarray-related invariants:
          @   (\forall int i; 0 <= i && i < top; i % 2 == 0 ==> permutation(array, \old(array), stack[i], stack[i+1])) &&
          @
          @   // Depth-related invariants:
          @   0 <= depth && depth <= depthLimit &&
          @   depthLimit >= 0 &&
          @   depthLimit == (int) (2 * Math.log(end - begin) / Math.log(2)) + 3 &&
          @
          @   // Begin and end invariants:
          @   0 <= begin && begin < end && end <= array.length &&
          @
          @   // The subarray [begin, end) at the top of the stack is always sorted.
          @   (\forall int i; begin <= i && i < end - 1; array[i] <= array[i + 1]);
          @
          @ // Termination measure:
          @ loop_decreases (depthLimit - depth) * array.length + (\sum int i; 0 <= i && i < top; i % 2 == 0 ? stack[i+1] - stack[i] : 0);
          @
          @ loop_modifies array[*], stack[*], top, depth, begin, end;
          @*/
        while (top > 0) {
            end = stack[--top];
            begin = stack[--top];

            /*@ loop_invariant stack != null && 0 <= top && top <= STACK_SIZE;
              @ loop_invariant top % 2 == 0; // The top index is always even
              @ loop_invariant 0 <= depth && depth <= depthLimit;
              @ loop_invariant 0 <= begin && begin < end && end <= array.length;
              @ // Stack holds valid indices
              @ loop_invariant (\forall int i; 0 <= i && i < top; stack[i] >= 0 && stack[i] < array.length);
              @ // Each segment in stack is sorted
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2;
              @                  (\forall int j; stack[2 * i] <= j && j < stack[2 * i + 1] - 1;
              @                   array[j] <= array[j + 1]));
              @ // Each segment is a valid permutation
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2;
              @                  (\forall int j; stack[2 * i] <= j && j < stack[2 * i + 1];
              @                   (\forall int k; stack[2 * i] <= k && k < stack[2 * i + 1]; array[k] == array[j] &&
              @                    (\num_of int l; stack[2 * i] <= l && l < stack[2 * i + 1]; array[l] == array[j]) ==
              @                    (\num_of int l; stack[2 * i] <= l && l < stack[2 * i + 1]; \old(array[l]) == array[j]))));
              @ // Adjacent segments are ordered
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2 - 1;
              @                  array[stack[2 * i + 1] - 1] <= array[stack[2 * (i + 1)]]);
              @ loop_decreases end - begin;
              @*/
            while (end - begin > IS_THRESH && depth < depthLimit) {
                int pivot = partition(array, begin, end);
                if (pivot - begin > end - pivot) {
                    stack[top++] = begin;
                    stack[top++] = pivot;
                    begin = pivot + 1;
                } else {
                    stack[top++] = pivot + 1;
                    stack[top++] = end;
                    end = pivot;
                }
                depth++;
            }

            if (end - begin <= IS_THRESH || depth >= depthLimit) {
                insertionSort(array, begin, end);
            }

            depth--;
        }
    }

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
        int depthLimit = (int) (2 * Math.log(end - begin) / Math.log(2)) + 3;
        quickSortRec(array, begin, end, depth, depthLimit);
    }

    /*@
      @ public normal_behavior
      @ requires array != null;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ requires 0 <= depth && depth <= depthLimit;
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
    public static void quickSortRec(int[] array, int begin, int end, int depth, int depthLimit) {

        if (end - begin <= IS_THRESH || depth >= depthLimit) {
            insertionSort(array, begin, end);
            return;
        }

        int pivot = partition(array, begin, end);
        quickSortRec(array, begin, pivot, depth + 1, depthLimit);
        quickSortRec(array, pivot + 1, end, depth + 1, depthLimit);
    }

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
    public static void insertionSort(int[] array, int begin, int end) {
        Arrays.sort(array, begin, end);
    }

    public static void quickSort(int[] array) {
        quickSort(array, 0, array.length);
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
      @ requires end - begin >= 3;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // Result is within the given range [begin, end)
      @ ensures \result == begin + ((end - begin) / 2);
      @
      @ // Result is a valid median.
      @ ensures array[begin] <= array[\result] && array[\result] <= array[end - 1];
      @
      @ // The values at 'begin', 'end - 1', and 'begin + ((end - begin) / 2)' are a permutations of the values before.
      @ ensures permutation(array, \old(array), begin, end);
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
      @ requires end - begin >= 3;
      @ requires 0 <= begin && begin < end && end <= array.length;
      @ ensures array.length == \old(array.length);
      @
      @ // The resulting pivot is inside the range [begin, end).
      @ ensures begin <= \result && \result < end;
      @
      @ // Values inside the range [begin, \result) are smaller than array[\result].
      @ ensures (\forall int i; begin <= i && i < \result; array[i] <= array[\result]);
      @ // Values inside the range (\result, end) are greater than array[\result].
      @ ensures (\forall int i; \result < i && i < end; array[\result] <= array[i]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ ensures permutation(array, \old(array), begin, end);
      @
      @ assignable array[begin .. end-1];
      @*/
    public static int partition(int[] array, int begin, int end) {
        int mid = medianOf3(array, begin, end);
        // TODO fails with begin + 1, end - 1. Why? Works with begin, end.
        return hoareBlockPartition(array, begin + 1, end - 1, mid);
    }

    /*@
      @ normal_behavior
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
        // /*@
        //   @ loop_invariant begin <= i && i <= end;
        //   @ loop_invariant (\forall int j; begin <= j && j < i; (
        //   @                 (\num_of int k; begin <= k && k < end; array1[j] == array1[k]) ==
        //   @                 (\num_of int k; begin <= k && k < end; array1[j] == array2[k])));
        //   @ loop_modifies i;
        //   @ loop_decreases end - i;
        //  */
        for (int i = begin; i < end; i++) {
            int count1 = 0;
            int count2 = 0;
            // /*@
            //   @ loop_invariant begin <= j && j <= end;
            //   @ loop_invariant count1 == (\num_of int k; begin <= k && k < j; array1[i] == array1[k]);
            //   @ loop_invariant count2 == (\num_of int k; begin <= k && k < j; array1[i] == array2[k]);
            //   @ loop_modifies j, count1, count2;
            //   @ loop_decreases end - j;
            //  */
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
