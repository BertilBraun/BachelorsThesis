import java.util.Arrays;
import java.util.Comparator;
import java.util.Random;

public class BlockQuickSort {

    private static final int BLOCKSIZE = 128;
    private static final int IS_THRESH = 16;
    private static final int STACK_SIZE = 80;

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= i && i < array.length;
     * @ requires 0 <= j && j < array.length;
     *
     * @ // Values at 'i' and 'j' are swapped.
     * @ ensures array[i] == \old(array[j]) && array[j] == \old(array[i]);
     *
     * @ // Values other than 'i' and 'j' remain unchanged.
     * @ ensures (\forall int k; 0 <= k && k < array.length && k != i && k != j; array[k] == \old(array[k]));
     * @ assignable array[i], array[j];
     */
    public static <T> void swap(T[] array, int i, int j) {
        T temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= begin && begin < end && end <= array.length;
     * @ requires 0 <= pivotPosition && pivotPosition < array.length;
     * @ requires \typeof(array) == \type(T[]);
     * @ requires comparator != null;
     *
     * @ // The resulting pivot is inside the range [begin, end).
     * @ ensures begin <= \result && \result < end;
     *
     * @ // Values inside the range [begin, \result) are smaller than array[\result].
     * @ ensures (\forall int i; begin <= i && i < \result;
     * @           comparator.compare(array[i], array[\result]) <= 0);
     * @ // Values inside the range (\result, end) are greater than array[\result].
     * @ ensures (\forall int i; \result < i && i < end;
     * @           comparator.compare(array[i], array[\result]) >= 0);
     *
     * @ // Values inside the range [begin, end) are a valid permutation.
     * @ ensures (\forall int i; begin <= i && i < end;
     * @          \num_of(int j; begin <= j && j < end && array[j] == array[i]) ==
     * @          \num_of(int j; begin <= j && j < end && \old(array[j]) == array[i]));
     *
     * @ // Values outside the range [begin, end) remain unchanged.
     * @ ensures (\forall int k; 0 <= k && k < array.length && (k < begin || k >= end); array[k] == \old(array[k]));
     * @ assignable array[begin .. end-1];
     */
    public static <T> int hoareBlockPartitionSimple(
            T[] array,
            int begin,
            int end,
            int pivotPosition,
            Comparator<T> comparator) {
        int[] indexL = new int[BLOCKSIZE];
        int[] indexR = new int[BLOCKSIZE];

        int last = end - 1;
        T pivot = array[pivotPosition];
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
                //@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                //@ loop_invariant 0 <= numLeft && numLeft <= j;
                //@ loop_invariant \num_of(int i; 0 <= i && i < j;
                //@                 comparator.compare(array[begin + i], pivot) >= 0) == numLeft;
                //@ loop_invariant \forall int k; 0 <= k && k < numLeft;
                //@                 0 <= indexL[k] && indexL[k] < BLOCKSIZE &&
                //@                 indexL[k] == (\num_of int l; 0 <= l && l < k;
                //@                                comparator.compare(array[begin + l], pivot) >= 0);
                //@ loop_invariant indexL[numLeft] == j;
                //@ loop_decreases BLOCKSIZE - j;
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexL[numLeft] = j;
                    numLeft += comparator.compare(array[begin + j], pivot) >= 0 ? 1 : 0;
                }
            }
            if (numRight == 0) {
                startRight = 0;
                //@ loop_invariant 0 <= j && j <= BLOCKSIZE;
                //@ loop_invariant 0 <= numRight && numRight <= j;
                //@ loop_invariant \num_of(int i; 0 <= i && i < j;
                //@                 comparator.compare(pivot, array[last - i]) >= 0) == numRight;
                //@ loop_invariant \forall int k; 0 <= k && k < numRight;
                //@                 0 <= indexR[k] && indexR[k] < BLOCKSIZE &&
                //@                 indexR[k] == (\num_of int l; 0 <= l && l < k;
                //@                                comparator.compare(pivot, array[last - l]) >= 0);
                //@ loop_invariant indexR[numRight] == j;
                //@ loop_decreases BLOCKSIZE - j;
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexR[numRight] = j;
                    numRight += comparator.compare(pivot, array[last - j]) >= 0 ? 1 : 0;
                }
            }

            num = Math.min(numLeft, numRight);
            //@ loop_invariant 0 <= j && j <= num;
            //@ loop_invariant begin + indexL[startLeft] <= begin + indexL[startLeft + j] &&
            //@                last - indexR[startRight] >= last - indexR[startRight + j];
            //@ loop_invariant \forall int k; 0 <= k && k < j;
            //@                 comparator.compare(array[begin + indexL[startLeft + k]], pivot) >= 0 &&
            //@                 comparator.compare(array[last - indexR[startRight + k]], pivot) <= 0;
            //@ loop_decreases num - j;
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
              @ loop_invariant \num_of(int i; 0 <= i && i < j;
              @                 comparator.compare(array[begin + i], pivot) >= 0) == numLeft;
              @ loop_invariant \forall int k; 0 <= k && k < numLeft;
              @                 0 <= indexL[k] && indexL[k] < shiftL &&
              @                 indexL[k] == (\num_of int l; 0 <= l && l < k;
              @                                comparator.compare(array[begin + l], pivot) >= 0);
              @ loop_invariant indexL[numLeft] == j;
              @ loop_invariant 0 <= numRight && numRight <= j;
              @ loop_invariant \num_of(int i; 0 <= i && i < j;
              @                 comparator.compare(pivot, array[last - i]) >= 0) == numRight;
              @ loop_invariant \forall int k; 0 <= k && k < numRight;
              @                 0 <= indexR[k] && indexR[k] < shiftL &&
              @                 indexR[k] == (\num_of int l; 0 <= l && l < k;
              @                                comparator.compare(pivot, array[last - l]) >= 0);
              @ loop_invariant indexR[numRight] == j;
              @ loop_decreases shiftL - j;
              @*/
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += comparator.compare(array[begin + j], pivot) >= 0 ? 1 : 0;
                indexR[numRight] = j;
                numRight += comparator.compare(pivot, array[last - j]) >= 0 ? 1 : 0;
            }
            if (shiftL < shiftR) {
                indexR[numRight] = shiftR - 1;
                numRight += comparator.compare(pivot, array[last - shiftR + 1]) >= 0 ? 1 : 0;
            }
        } else if (numRight != 0) {
            shiftL = (last - begin) - BLOCKSIZE + 1;
            shiftR = BLOCKSIZE;
            startLeft = 0;
            //@ loop_invariant 0 <= j && j <= shiftL;
            //@ loop_invariant 0 <= numLeft && numLeft <= j;
            //@ loop_invariant \num_of(int i; 0 <= i && i < j;
            //@                 comparator.compare(array[begin + i], pivot) >= 0) == numLeft;
            //@ loop_invariant \forall int k; 0 <= k && k < numLeft;
            //@                 0 <= indexL[k] && indexL[k] < shiftL &&
            //@                 indexL[k] == (\num_of int l; 0 <= l && l < k;
            //@                                comparator.compare(array[begin + l], pivot) >= 0);
            //@ loop_invariant indexL[numLeft] == j;
            //@ loop_decreases shiftL - j;
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += comparator.compare(array[begin + j], pivot) >= 0 ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;
            //@ loop_invariant 0 <= j && j <= shiftR;
            //@ loop_invariant 0 <= numRight && numRight <= j;
            //@ loop_invariant \num_of(int i; 0 <= i && i < j;
            //@                 comparator.compare(pivot, array[last - i]) >= 0) == numRight;
            //@ loop_invariant \forall int k; 0 <= k && k < numRight;
            //@                 0 <= indexR[k] && indexR[k] < shiftR &&
            //@                 indexR[k] == (\num_of int l; 0 <= l && l < k;
            //@                                comparator.compare(pivot, array[last - l]) >= 0);
            //@ loop_invariant indexR[numRight] == j;
            //@ loop_decreases shiftR - j;
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += comparator.compare(pivot, array[last - j]) >= 0 ? 1 : 0;
            }
        }

        num = Math.min(numLeft, numRight);
        //@ loop_invariant 0 <= j && j <= num;
        //@ loop_invariant begin + indexL[startLeft] <= begin + indexL[startLeft + j] &&
        //@                last - indexR[startRight] >= last - indexR[startRight + j];
        //@ loop_invariant \forall int k; 0 <= k && k < j;
        //@                 comparator.compare(array[begin + indexL[startLeft + k]], pivot) >= 0 &&
        //@                 comparator.compare(array[last - indexR[startRight + k]], pivot) <= 0;
        //@ loop_invariant (\forall int i; begin <= i && i < begin + indexL[startLeft + j];
        //@                  comparator.compare(array[i], array[begin + indexL[startLeft + j]]) <= 0);
        //@ loop_invariant (\forall int i; last - indexR[startRight + j] < i && i <= last;
        //@                  comparator.compare(array[i], array[last - indexR[startRight + j]]) >= 0);
        //@ loop_invariant \num_of(int l; begin <= l && l < begin + indexL[startLeft + j];
        //@                  comparator.compare(array[l], pivot) >= 0) ==
        //@                  num - (\num_of int m; 0 <= m && m < j;
        //@                         comparator.compare(array[begin + indexL[startLeft + m]], pivot) >= 0);
        //@ loop_invariant \num_of(int l; last - indexR[startRight + j] < l && l <= last;
        //@                  comparator.compare(pivot, array[l]) >= 0) ==
        //@                  num - (\num_of int m; 0 <= m && m < j;
        //@                         comparator.compare(pivot, array[last - indexR[startRight + m]]) >= 0);
        //@ loop_decreases num - j;
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

            //@ loop_invariant 0 <= lowerI && lowerI >= startLeft;
            //@ loop_invariant 0 <= upper && upper <= last - begin;
            //@ loop_invariant upper == last - begin - numLeft + 1 + lowerI;
            //@ loop_decreases lowerI - startLeft + 1;
            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant startLeft <= lowerI && lowerI < BLOCKSIZE;
            //@ loop_invariant begin + indexL[lowerI] <= begin + indexL[startLeft] + upper;
            //@ loop_invariant \forall int k; startLeft <= k && k < lowerI;
            //@                 comparator.compare(array[begin + indexL[k]], pivot) >= 0 &&
            //@                 comparator.compare(array[begin + indexL[k] + 1], pivot) <= 0;
            //@ loop_decreases lowerI - startLeft;
            while (lowerI >= startLeft) {
                swap(array, begin + upper--, begin + indexL[lowerI--]);
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            //@ loop_invariant 0 <= lowerI && lowerI >= startRight;
            //@ loop_invariant upper == last - begin - (numRight - 1) + (startRight - lowerI);
            //@ loop_invariant \forall int k; startRight <= k && k <= lowerI; indexR[k] == upper + (lowerI - k);
            //@ loop_decreases lowerI - startRight + 1;
            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            //@ loop_invariant 0 <= lowerI && lowerI >= startRight;
            //@ loop_invariant upper == last - begin - (numRight - 1) + (startRight - lowerI);
            //@ loop_invariant \forall int k; startRight <= k && k <= lowerI;
            //@                 comparator.compare(array[last - indexR[k]], pivot) <= 0 &&
            //@                 comparator.compare(array[last - upper - (lowerI - k)], pivot) >= 0;
            //@ loop_decreases lowerI - startRight + 1;
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

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= i1 && i1 < array.length;
     * @ requires 0 <= i2 && i2 < array.length;
     * @ requires comparator != null;
     * @ requires \typeof(array) == \type(T[]);
     *
     * @ // Values at 'i1' and 'i2' are the old values but now sorted.
     * @ ensures (comparator.compare(\old(array[i1]), \old(array[i2])) <= 0)    ?
     * @         (array[i1] == \old(array[i1]) && array[i2] == \old(array[i2])) :
     * @         (array[i1] == \old(array[i2]) && array[i2] == \old(array[i1]));
     *
     * @ // Values other than 'i1' and 'i2' remain unchanged.
     * @ ensures (\forall int k; 0 <= k && k < array.length && k != i1 && k != i2; array[k] == \old(array[k]));
     * @ assignable array[i1], array[i2];
     */
    public static <T> void sortPair(int i1, int i2, T[] array, Comparator<T> comparator) {
        boolean smaller = comparator.compare(array[i2], array[i1]) < 0;
        T temp = smaller ? array[i1] : array[i2];
        array[i1] = smaller ? array[i2] : array[i1];
        array[i2] = smaller ? temp : array[i2];
    }

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= begin && begin < end && end <= array.length;
     * @ requires comparator != null;
     * @ requires \typeof(array) == \type(T[]);
     *
     * @ // Result is within the given range [begin, end)
     * @ ensures 0 <= \result && \result < array.length;
     * @ ensures begin <= \result && \result < end;
     *
     * @ // Result is a valid median.
     * @ ensures comparator.compare(array[begin], array[\result]) <= 0 &&
     * @         comparator.compare(array[\result], array[end - 1]) <= 0;
     *
     * @ // The values at 'begin', 'end - 1', and 'begin + ((end - begin) / 2)' are a permutations of the values before.
     * @ ensures (\forall int i; i == begin || i == end - 1 || i == begin + ((end - begin) / 2);
     * @          \num_of(int j; (j == begin || j == end - 1 || j == begin + ((end - begin) / 2)) &&
     * @                          array[j] == array[i]) ==
     * @          \num_of(int j; (j == begin || j == end - 1 || j == begin + ((end - begin) / 2)) &&
     * @                         \old(array[j]) == array[i]));
     *
     * @ // Values other than 'begin', 'end - 1' and 'begin + ((end - begin) / 2)' remain unchanged.
     * @ ensures (\forall int i; begin <= i && i < end && i != begin && i != end - 1 && i != begin + ((end - begin) / 2);
     * @          array[i] == \old(array[i]));
     *
     * @ assignable array[begin], array[begin + ((end - begin) / 2)], array[end - 1];
     */
    public static <T> int medianOf3(T[] array, int begin, int end, Comparator<T> comparator) {
        int mid = begin + ((end - begin) / 2);
        sortPair(begin, mid, array, comparator);
        sortPair(mid, end - 1, array, comparator);
        sortPair(begin, mid, array, comparator);
        return mid;
    }

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= begin && begin < end && end <= array.length;
     * @ requires comparator != null;
     * @ requires \typeof(array) == \type(T[]);
     *
     * @ // The resulting pivot is inside the range [begin, end).
     * @ ensures begin <= \result && \result < end;
     *
     * @ // Values inside the range [begin, \result) are smaller than array[\result].
     * @ ensures (\forall int i; begin <= i && i < \result;
     * @           comparator.compare(array[i], array[\result]) <= 0);
     * @ // Values inside the range (\result, end) are greater than array[\result].
     * @ ensures (\forall int i; \result < i && i < end;
     * @           comparator.compare(array[i], array[\result]) >= 0);
     *
     * @ // Values inside the range [begin, end) are a valid permutation.
     * @ ensures (\forall int i; begin <= i && i < end;
     * @          \num_of(int j; begin <= j && j < end && array[j] == array[i]) ==
     * @          \num_of(int j; begin <= j && j < end && \old(array[j]) == array[i]));
     *
     * @ // Values outside the range [begin, end) remain unchanged.
     * @ ensures (\forall int k; 0 <= k && k < array.length && (k < begin || k >= end); array[k] == \old(array[k]));
     * @ assignable array[begin .. end-1];
     */
    public static <T> int partition(T[] array, int begin, int end, Comparator<T> comparator) {
        int mid = medianOf3(array, begin, end, comparator);
        return hoareBlockPartitionSimple(array, begin + 1, end - 1, mid, comparator);
    }

    /*
     * @ public normal_behavior
     * @ requires array != null;
     * @ requires 0 <= begin && begin < end && end <= array.length;
     * @ requires comparator != null;
     * @ requires \typeof(array) == \type(T[]);
     *
     * @ // Values inside the range [begin, end) are in sorted order.
     * @ ensures (\forall int i; 0 <= i && i < array.length - 1;
     * @           comparator.compare(array[i], array[i+1]) <= 0);
     *
     * @ // Values inside the range [begin, end) are a valid permutation.
     * @ ensures (\forall int i; begin <= i && i < end;
     * @          \num_of(int j; begin <= j && j < end && array[j] == array[i]) ==
     * @          \num_of(int j; begin <= j && j < end && \old(array[j]) == array[i]));
     *
     * @ // Values outside the range [begin, end) remain unchanged.
     * @ ensures (\forall int k; 0 <= k && k < array.length && (k < begin || k >= end); array[k] == \old(array[k]));
     * @ assignable array[begin .. end-1];
     */
    public static <T> void quickSort(T[] array, int begin, int end, Comparator<T> comparator) {
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
          @   (\forall int i; 0 <= i && i < top; 0 <= stack[i] && stack[i] <= array.length) &&
          @   (\forall int i; 0 <= i && i < top - 1; i += 2; stack[i+1] > stack[i]) &&
          @
          @   // Subarray-related invariants:
          @   (\forall int i; 0 <= i && i < top - 1; i += 2;
          @     (\forall int j, k; stack[i] <= j && j < k && k < stack[i+1];
          @       \num_of(int l; stack[i] <= l && l < stack[i+1] && array[l] == array[j]) ==
          @       \num_of(int l; stack[i] <= l && l < stack[i+1] && \old(array[l]) == array[j]))) &&
          @
          @   // Depth-related invariants:
          @   0 <= depth &&
          @   depthLimit >= 0 &&
          @   depth <= depthLimit &&
          @   depthLimit == (int) (2 * Math.log(end - begin) / Math.log(2)) + 3 &&
          @
          @   // Begin and end invariants:
          @   0 <= begin && begin <= end && end <= array.length &&
          @
          @   // Array-related invariants:
          @   array != null && \typeof(array) == \type(T[]) &&
          @   (\forall int i, j; 0 <= i && i < j && j < array.length;
          @     comparator.compare(array[i], array[j]) <= 0) &&
          @   (\forall int i; 0 <= i && i < array.length;
          @     \num_of(int j; 0 <= j && j < array.length && array[j] == array[i]) ==
          @     \num_of(int j; 0 <= j && j < array.length && \old(array[j]) == array[i])) &&
          @   (\forall int k; 0 <= k && k < array.length && (k < begin || k >= end); array[k] == \old(array[k]));
          @
          @   // The subarray [begin, end) at the top of the stack is always sorted.
          @   (\forall int i, j; begin <= i && i < j && j < end;
          @     comparator.compare(array[i], array[j]) <= 0);
          @
          @ loop_variant
          @   // Termination measure:
          @   (\sum int i; 0 <= i && i < top; stack[i]) - (end - begin);
          @ assignable array[begin .. end-1], stack[0 .. top-1], top, depth, begin, end;
          @*/
        do {
            end = stack[--top];
            begin = stack[--top];

            /*@ loop_invariant stack != null && 0 <= top && top <= STACK_SIZE;
              @ loop_invariant top % 2 == 0; // The top index is always even
              @ loop_invariant 0 <= depth && depth <= depthLimit;
              @ loop_invariant 0 <= begin && begin < end && end <= array.length;
              // Stack holds valid indices
              @ loop_invariant (\forall int i; 0 <= i && i < top; stack[i] >= 0 && stack[i] < array.length);
              // Each segment in stack is sorted
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2;
              @                  (\forall int j; stack[2 * i] <= j && j < stack[2 * i + 1] - 1;
              @                   comparator.compare(array[j], array[j + 1]) <= 0));
              // Each segment is a valid permutation
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2;
              @                  (\forall int j; stack[2 * i] <= j && j < stack[2 * i + 1];
              @                   (\forall int k; stack[2 * i] <= k && k < stack[2 * i + 1] && array[k] == array[j];
              @                    \num_of(int l; stack[2 * i] <= l && l < stack[2 * i + 1] && array[l] == array[j]) ==
              @                    \num_of(int l; stack[2 * i] <= l && l < stack[2 * i + 1] && \old(array[l]) == array[j]))));
              // Adjacent segments are ordered
              @ loop_invariant (\forall int i; 0 <= i && i < top / 2 - 1;
              @                  comparator.compare(array[stack[2 * i + 1] - 1], array[stack[2 * (i + 1)]]) <= 0);
              @ loop_decreases end - begin;
              @*/
            while (end - begin > IS_THRESH) {
                if (depth < depthLimit) {
                    int pivot = partition(array, begin, end, comparator);
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
                } else {
                    Arrays.sort(array, begin, end, comparator);
                    break;
                }
            }

            if (end - begin <= IS_THRESH) {
                Arrays.sort(array, begin, end, comparator);
            }

            depth--;

        } while (top > 0);
    }

    public static <T> void quickSort(T[] array, Comparator<T> comparator) {
        quickSort(array, 0, array.length, comparator);
    }

    public static void main(String[] args) {
        BlockQuickSortTest.runAllTests();
    }
}

class BlockQuickSortTest {

    public static void testQuickSortEmptyArray() {
        Integer[] array = new Integer[]{};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{}, array);
    }

    public static void testQuickSortSingleElement() {
        Integer[] array = new Integer[]{3};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{3}, array);
    }

    public static void testQuickSortSortedArray() {
        Integer[] array = new Integer[]{1, 2, 3, 4, 5};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{1, 2, 3, 4, 5}, array);
    }

    public static void testQuickSortReverseSortedArray() {
        Integer[] array = new Integer[]{5, 4, 3, 2, 1};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{1, 2, 3, 4, 5}, array);
    }

    public static void testQuickSortArrayWithDuplicates() {
        Integer[] array = new Integer[]{3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9}, array);
    }

    public static void testQuickSortArrayWithNegativeElements() {
        Integer[] array = new Integer[]{-5, 3, -1, 2, -8, 0};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{-8, -5, -1, 0, 2, 3}, array);
    }

    public static void testQuickSortArrayWithSameElements() {
        Integer[] array = new Integer[]{7, 7, 7, 7, 7, 7, 7};
        BlockQuickSort.quickSort(array, Integer::compare);
        assertArrayEquals(new Integer[]{7, 7, 7, 7, 7, 7, 7}, array);
    }

    public static void testQuickSortArrayWithRandomElements() {
        Integer[] array = new Random().ints(1000, 0, 10000).boxed().toArray(Integer[]::new);
        Integer[] arrayCopy = array.clone();
        BlockQuickSort.quickSort(array, Integer::compare);
        Arrays.sort(arrayCopy, Integer::compare);
        assertArrayEquals(arrayCopy, array);
    }

    public static void assertArrayEquals(Integer[] expected, Integer[] actual) {
        if (!Arrays.equals(expected, actual)) {
            System.out.println("expected: " + Arrays.toString(expected) + " but was: " + Arrays.toString(actual));
        }
    }

    public static void runAllTests() {
        testQuickSortEmptyArray();
        testQuickSortSingleElement();
        testQuickSortSortedArray();
        testQuickSortReverseSortedArray();
        testQuickSortArrayWithDuplicates();
        testQuickSortArrayWithNegativeElements();
        testQuickSortArrayWithSameElements();
        testQuickSortArrayWithRandomElements();
    }
}
