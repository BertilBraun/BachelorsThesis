public class Testing {
    public static final int N = 3;

    /*@ normal_behavior
      @ requires array != null && array.length <= N;
      @ ensures \result == (\num_of int i; 0 <= i < array.length; array[i] > 0);
      @*/
    public int testUnwinding(int[] array) {
        int[] newArray = new int[array.length * 2];
        for (int i = 0; i < array.length; i++) {
            newArray[2 * i] = array[i];
            newArray[2 * i + 1] = array[i];
        }
        return testUnwindingSub(newArray) / 2;
    }

    /*@ normal_behavior
      @ requires array != null && array.length <= N;
      @ ensures \result == (\num_of int i; 0 <= i < array.length; array[i] > 0);
      @ pure
      @*/
    public int testUnwindingSub(int[] array) {
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
      @ ensures \result == (\num_of int i; 0 <= i < array.length; array[i] > 0);
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
      @ ensures \result == (\sum int i; 0 <= i < array.length; array[i]);
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
      @ ensures \result == (\sum int i; 0 <= i < array.length; (\num_of int j; i <= j < array.length; array[j] < array[i]));
      @*/
    public int testSumNumOf(int[] array) {
        int sum = 0;
        for (int i = 0; i < array.length; i++) {
            for (int j = i; j < array.length; j++) {
                if (array[j] < array[i]) {
                    sum++;
                }
            }
        }
        return sum;
    }

    /*@ normal_behavior
      @ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; \forall int j; i <= j < array.length; array[i] <= array[j]);
      @ ensures \result == (\forall int i; 0 <= i < array.length; \forall int j; i <= j < array.length; array[i] <= array[j]);
      @*/
    public boolean testForFor(int[] array) {
        for (int i = 0; i < array.length; i++) {
            for (int j = i; j < array.length; j++) {
                if (array[i] > array[j]) {
                    return false;
                }
            }
        }
        return true;
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
    public void testAssignmentIssues(int[] array, int[] b) {
        array[3] = 0;
        b[1] = 0;
    }

    //@ requires array != null && array.length > 0;
    //@ ensures \result == (\min int i; 0 <= i < array.length; array[i]);
    public int testMin(int[] array) {
        int minValue = array[0];
        for (int i = 1; i < array.length; i++) {
            if (array[i] < minValue) {
                minValue = array[i];
            }
        }
        return minValue;
    }

    //@ requires array != null && array.length > 0;
    //@ ensures \result == (\max int i; 0 <= i < array.length; array[i]);
    public int testMax(int[] array) {
        int maxValue = array[0];
        for (int i = 1; i < array.length; i++) {
            if (array[i] > maxValue) {
                maxValue = array[i];
            }
        }
        return maxValue;
    }

    //@ requires array != null && array.length == 0;
    //@ ensures \result == (\min int i; 0 <= i < array.length; array[i]);
    public int testMinEmptyArray(int[] array) {
        return Integer.MAX_VALUE;
    }

    //@ requires array != null && array.length == 0;
    //@ ensures \result == (\max int i; 0 <= i < array.length; array[i]);
    public int testMaxEmptyArray(int[] array) {
        return Integer.MIN_VALUE;
    }

}
