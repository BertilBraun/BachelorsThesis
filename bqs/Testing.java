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
}
