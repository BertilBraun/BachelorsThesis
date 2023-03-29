public class BlockQuickSortTest {

    private static final int BLOCKSIZE = 128;
    private static final int IS_THRESH = 4;
    private static final int STACK_SIZE = 80;

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
      @ ensures (\old(array[i1]) <= \old(array[i2]))    ?
      @         (array[i1] == \old(array[i1]) && array[i2] == \old(array[i2])) :
      @         (array[i1] == \old(array[i2]) && array[i2] == \old(array[i1]));
      @
      @ assignable array[i1], array[i2];
      @*/
    public static void sortPair(int i1, int i2, int[] array) {
        if (array[i2] < array[i1]) {
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
      @ ensures begin <= \result && \result < end;
      @ ensures \result == begin + ((end - begin) / 2);
      @
      @ // Result is a valid median.
      @ ensures array[begin] <= array[\result] && array[\result] <= array[end - 1];
      @
      @
      @ // The values at 'begin', 'end - 1', and 'begin + ((end - begin) / 2)' are a permutations of the values before.
      @ // ensures (\forall int i; i == begin || i == end - 1 || i == begin + ((end - begin) / 2);
      @ //          \num_of(int j; (j == begin || j == end - 1 || j == begin + ((end - begin) / 2)) &&
      @ //                          array[j] == array[i]) ==
      @ //          \num_of(int j; (j == begin || j == end - 1 || j == begin + ((end - begin) / 2)) &&
      @ //                         \old(array[j]) == array[i]));
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
      @ requires begin <= pivotPosition && pivotPosition < end;
      @ ensures array.length == \old(array.length);
      @
      @ // The resulting pivot is inside the range [begin, end).
      @ ensures begin <= \result && \result < end;
      @
      @ // Values inside the range [begin, \result) are smaller than array[\result].
      @ ensures (\forall int i; begin <= i && i < \result; array[i] <= array[\result]);
      @ // Values inside the range (\result, end) are greater than array[\result].
      @ ensures (\forall int i; \result < i && i < end; array[i] >= array[\result]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ // ensures (\forall int i; begin <= i && i < end;
      @ //          \num_of(int j; begin <= j && j < end && array[j] == array[i]) ==
      @ //          \num_of(int j; begin <= j && j < end && \old(array[j]) == array[i]));
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

        while (last - begin + 1 > 2 * BLOCKSIZE) {
            if (numLeft == 0) {
                startLeft = 0;
                /*@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                  @ loop_invariant 0 <= numLeft && numLeft <= j;
                  @ // loop_invariant \num_of(int i; 0 <= i && i < j;
                  @ //                 array[begin + i] >= pivot) == numLeft;
                  @ // loop_invariant \forall int k; 0 <= k && k < numLeft;
                  @ //                 0 <= indexL[k] && indexL[k] < BLOCKSIZE &&
                  @ //                 indexL[k] == (\num_of int l; 0 <= l && l < k;
                  @ //                                array[begin + l] >= pivot);
                  @ loop_invariant indexL[numLeft] == j;
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
                  @ loop_invariant 0 <= numRight && numRight <= j;
                  @ // loop_invariant \num_of(int i; 0 <= i && i < j;
                  @ //                 pivot >= array[last - i]) == numRight;
                  @ // loop_invariant \forall int k; 0 <= k && k < numRight;
                  @ //                 0 <= indexR[k] && indexR[k] < BLOCKSIZE &&
                  @ //                 indexR[k] == (\num_of int l; 0 <= l && l < k;
                  @ //                                pivot >= array[last - l]);
                  @ loop_invariant indexR[numRight] == j;
                  @ loop_decreases BLOCKSIZE - j;
                  @*/
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexR[numRight] = j;
                    numRight += pivot >= array[last - j] ? 1 : 0;
                }
            }

            num = Math.min(numLeft, numRight);
            /*@ loop_invariant 0 <= j && j <= num;
              @ loop_invariant begin + indexL[startLeft] <= begin + indexL[startLeft + j] &&
              @                last - indexR[startRight] >= last - indexR[startRight + j];
              @ loop_invariant \forall int k; 0 <= k && k < j;
              @                 array[begin + indexL[startLeft + k]] >= pivot &&
              @                 array[last - indexR[startRight + k]] <= pivot;
              @ loop_decreases num - j;
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
              @ // loop_invariant \num_of(int i; 0 <= i && i < j;
              @ //                 array[begin + i] >= pivot) == numLeft;
              @ // loop_invariant \forall int k; 0 <= k && k < numLeft;
              @ //                 0 <= indexL[k] && indexL[k] < shiftL &&
              @ //                 indexL[k] == (\num_of int l; 0 <= l && l < k;
              @ //                                array[begin + l] >= pivot);
              @ loop_invariant indexL[numLeft] == j;
              @ loop_invariant 0 <= numRight && numRight <= j;
              @ // loop_invariant \num_of(int i; 0 <= i && i < j;
              @ //                 pivot >= array[last - i]) == numRight;
              @ // loop_invariant \forall int k; 0 <= k && k < numRight;
              @ //                 0 <= indexR[k] && indexR[k] < shiftL &&
              @ //                 indexR[k] == (\num_of int l; 0 <= l && l < k;
              @ //                                pivot >= array[last - l]);
              @ loop_invariant indexR[numRight] == j;
              @ loop_decreases shiftL - j;
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
              @ loop_invariant 0 <= numLeft && numLeft <= j;
              @ // loop_invariant \num_of(int i; 0 <= i && i < j;
              @ //                 array[begin + i] >= pivot) == numLeft;
              @ // loop_invariant \forall int k; 0 <= k && k < numLeft;
              @ //                 0 <= indexL[k] && indexL[k] < shiftL &&
              @ //                 indexL[k] == (\num_of int l; 0 <= l && l < k;
              @ //                                array[begin + l] >= pivot);
              @ loop_invariant indexL[numLeft] == j;
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
              @ // loop_invariant \num_of(int i; 0 <= i && i < j;
              @ //                 pivot >= array[last - i]) == numRight;
              @ // loop_invariant \forall int k; 0 <= k && k < numRight;
              @ //                 0 <= indexR[k] && indexR[k] < shiftR &&
              @ //                 indexR[k] == (\num_of int l; 0 <= l && l < k;
              @ //                                pivot >= array[last - l]);
              @ loop_invariant indexR[numRight] == j;
              @ loop_decreases shiftR - j;
              @*/
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
        }

        num = Math.min(numLeft, numRight);
        /*@ loop_invariant 0 <= j && j <= num;
          @ loop_invariant begin + indexL[startLeft] <= begin + indexL[startLeft + j] &&
          @                last - indexR[startRight] >= last - indexR[startRight + j];
          @ loop_invariant \forall int k; 0 <= k && k < j;
          @                 array[begin + indexL[startLeft + k]] >= pivot &&
          @                 array[last - indexR[startRight + k]] <= pivot;
          @ loop_invariant (\forall int i; begin <= i && i < begin + indexL[startLeft + j];
          @                  array[i] <= array[begin + indexL[startLeft + j]]);
          @ loop_invariant (\forall int i; last - indexR[startRight + j] < i && i <= last;
          @                  array[i] >= array[last - indexR[startRight + j]]);
          @ // loop_invariant \num_of(int l; begin <= l && l < begin + indexL[startLeft + j];
          @ //                  array[l] >= pivot) ==
          @ //                  num - (\num_of int m; 0 <= m && m < j;
          @ //                         array[begin + indexL[startLeft + m]] >= pivot);
          @ // loop_invariant \num_of(int l; last - indexR[startRight + j] < l && l <= last;
          @ //                  pivot >= array[l]) ==
          @ //                  num - (\num_of int m; 0 <= m && m < j;
          @ //                         pivot >= array[last - indexR[startRight + m]]);
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

            /*@ loop_invariant 0 <= lowerI && lowerI >= startLeft;
              @ loop_invariant 0 <= upper && upper <= last - begin;
              @ loop_invariant upper == last - begin - numLeft + 1 + lowerI;
              @ loop_decreases lowerI - startLeft + 1;
              @*/
            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            /*@ loop_invariant startLeft <= lowerI && lowerI < BLOCKSIZE;
              @ loop_invariant begin + indexL[lowerI] <= begin + indexL[startLeft] + upper;
              @ loop_invariant \forall int k; startLeft <= k && k < lowerI;
              @                 array[begin + indexL[k]] >= pivot &&
              @                 array[begin + indexL[k] + 1] <= pivot;
              @ loop_decreases lowerI - startLeft;
              @*/
            while (lowerI >= startLeft) {
                swap(array, begin + upper--, begin + indexL[lowerI--]);
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            /*@ loop_invariant 0 <= lowerI && lowerI >= startRight;
              @ loop_invariant upper == last - begin - (numRight - 1) + (startRight - lowerI);
              @ loop_invariant \forall int k; startRight <= k && k <= lowerI; indexR[k] == upper + (lowerI - k);
              @ loop_decreases lowerI - startRight + 1;
              @*/
            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            /*@ loop_invariant 0 <= lowerI && lowerI >= startRight;
              @ loop_invariant upper == last - begin - (numRight - 1) + (startRight - lowerI);
              @ loop_invariant \forall int k; startRight <= k && k <= lowerI;
              @                 array[last - indexR[k]] <= pivot &&
              @                 array[last - upper - (lowerI - k)] >= pivot;
              @ loop_decreases lowerI - startRight + 1;
              @*/
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
      @ ensures (\forall int i; \result < i && i < end; array[i] >= array[\result]);
      @
      @ // Values inside the range [begin, end) are a valid permutation.
      @ // ensures (\forall int i; begin <= i && i < end;
      @ //          \num_of(int j; begin <= j && j < end && array[j] == array[i]) ==
      @ //          \num_of(int j; begin <= j && j < end && \old(array[j]) == array[i]));
      @
      @ assignable array[begin .. end-1];
      @*/
    public static int partition(int[] array, int begin, int end) {
        int mid = medianOf3(array, begin, end);
        // TODO check, begin + 1, end - 1 is incorrect. With begin and end it is correct. Probably requiring permutation.
        return hoareBlockPartition(array, begin + 1, end - 1, mid);
    }
}
