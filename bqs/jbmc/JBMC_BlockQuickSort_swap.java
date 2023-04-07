import org.cprover.CProver;

public class JBMC_BlockQuickSort_swap {

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

        CProver.assume(i >= 0 && i < array.length);
        CProver.assume(j >= 0 && j < array.length);
        CProver.assume(array != null);

        int oldi = array[i];
        int oldj = array[j];

        int temp = array[i];
        array[i] = array[j];
        array[j] = temp;

        assert (array[i] == oldj);
        assert (array[j] == oldi);
    }
}
