public class BlockQuickSortTest {

    private static final int BLOCKSIZE = 128;
    private static final int IS_THRESH = 16;
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

}
