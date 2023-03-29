import java.util.function.IntFunction;
import java.util.function.IntPredicate;

public class Testing {

    public static class Inner {

        /*@ normal_behavior
          @ requires array != null;
          @ requires rangePredicate != null;
          @ requires targetPredicate != null;
          @ requires function != null;
          @ assignable \nothing;
          @ pure
          @*/
        public static int sum(int[] array, IntPredicate rangePredicate, IntPredicate targetPredicate,
                IntFunction function) {
            int sum = 0;
            for (int i = 0; i < array.length; i++) {
                if (rangePredicate.test(i) && targetPredicate.test(array[i])) {
                    sum += (int) function.apply(array[i]);
                }
            }
            return sum;
        }

        /*@ normal_behavior
          @ requires array != null;
          @ requires rangePredicate != null;
          @ requires targetPredicate != null;
          @ assignable \nothing;
          @ pure
          @*/
        public static int numOf(int[] array, IntPredicate rangePredicate, IntPredicate targetPredicate) {
            return sum(array, rangePredicate, targetPredicate, x -> 1);
        }
    }

    /*@ normal_behavior
      @ requires array != null;
      @ ensures \result == Inner.sum(array, (x -> 0 <= x && x < array.length), (y -> y > 0), (z -> z));
      @*/
    public int sumTest(int[] array) {
        int sum = 0;
        for (int i = 0; i < array.length; i++) {
            if (array[i] > 0) {
                sum += array[i];
            }
        }
        return sum;
    }

}
