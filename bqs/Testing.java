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

    /*@ public normal_behavior
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
        boolean result = true;
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
                result = false;
                return false;
            }
        }
        return true;
    }
}
