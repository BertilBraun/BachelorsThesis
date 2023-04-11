public class Testing {

    /*@ normal_behavior
      @ requires array != null;
      @ ensures \result == (\num_of int i; 0 <= i && i < array.length; array[i] > 0);
      @*/
    public int testNumOf(int[] array) {
        int count = 0;
        for (int i = 0; i < array.length; i++) {
            if (array[i] > 0) {
                count++;
            }
        }
        return count;
    }

    /*@ normal_behavior
      @ requires array != null;
      @ ensures \result == (\sum int i; 0 <= i && i < array.length; array[i]);
      @*/
    public int testSum(int[] array) {
        int sum = 0;
        for (int i = 0; i < array.length; i++) {
            sum += array[i];
        }
        return sum;
    }

    /*@ normal_behavior
      @ requires array != null;
      @ requires array.length > 3;
      @ requires b != null;
      @ requires b.length > 3;
      @ ensures array[3] == 0;
      @ ensures b[1] == 0;
      @ assignable array[1..2];
      @*/
    public void test(int[] array, int[] b) {
        array[3] = 0;
        b[1] = 0;
    }

    /*@
    @ public normal_behavior
    @ requires array != null && array.length < 500;
    @ requires (originalEnd - originalBegin) >= 1;
    @ requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length;
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
        return 0;
    }

    /*@
      @ public normal_behavior
      @ requires array != null && array.length < 500;
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
      @ ensures (\forall int i; begin <= i && i < end; (
      @          (\num_of int j; begin <= j && j < end; array[i] == array[j]) ==
      @          (\num_of int j; begin <= j && j < end; array[i] == \old(array[j]))
      @         ));
      @
      @ assignable array[begin], array[begin + ((end - begin) / 2)], array[end - 1];
      @*/
    public static int medianOf3(int[] array, int begin, int end) {
        return 0;
    }

    /*@
      @ public normal_behavior
      @ requires array != null && array.length < 500;
      @ requires end - begin >= 3;
      @ requires 0 <= begin && begin < end && end <= array.length;
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
        /*@
          @ loop_invariant begin <= i && i <= end;
          @ loop_invariant (\forall int j; begin <= j && j < i; (
          @                 (\num_of int k; begin <= k && k < end; array1[j] == array1[k]) ==
          @                 (\num_of int k; begin <= k && k < end; array1[j] == array2[k])
          @                ));
          @ loop_modifies i;
          @ loop_decreases end - i;
         */
        for (int i = begin; i < end; i++) {
            int count1 = 0;
            int count2 = 0;
            /*@
              @ loop_invariant begin <= j && j <= end;
              @ loop_invariant count1 == (\num_of int k; begin <= k && k < j; array1[i] == array1[k]);
              @ loop_invariant count2 == (\num_of int k; begin <= k && k < j; array1[i] == array2[k]);
              @ loop_modifies j, count1, count2;
              @ loop_decreases end - j;
             */
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
