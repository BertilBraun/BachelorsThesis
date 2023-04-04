import java.util.Arrays;
import java.util.Random;

class BlockQuickSortTest {

    public static void main(String[] args) {
        BlockQuickSortTest.runAllTests();
    }

    public static void testQuickSortEmptyArray() {
        int[] array = new int[] {};
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] {}, array);
    }

    public static void testQuickSortSingleElement() {
        int[] array = new int[] { 3 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { 3 }, array);
    }

    public static void testQuickSortSortedArray() {
        int[] array = new int[] { 1, 2, 3, 4, 5 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { 1, 2, 3, 4, 5 }, array);
    }

    public static void testQuickSortReverseSortedArray() {
        int[] array = new int[] { 5, 4, 3, 2, 1 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { 1, 2, 3, 4, 5 }, array);
    }

    public static void testQuickSortArrayWithDuplicates() {
        int[] array = new int[] { 3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { 1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9 }, array);
    }

    public static void testQuickSortArrayWithNegativeElements() {
        int[] array = new int[] { -5, 3, -1, 2, -8, 0 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { -8, -5, -1, 0, 2, 3 }, array);
    }

    public static void testQuickSortArrayWithSameElements() {
        int[] array = new int[] { 7, 7, 7, 7, 7, 7, 7 };
        BlockQuickSort.quickSort(array);
        assertArrayEquals(new int[] { 7, 7, 7, 7, 7, 7, 7 }, array);
    }

    public static void testQuickSortArrayWithRandomElements() {
        int[] array = new Random().ints(1000, 0, 10000).boxed().mapToInt(Integer::intValue).toArray();
        int[] arrayCopy = array.clone();
        BlockQuickSort.quickSort(array);
        Arrays.sort(arrayCopy);
        assertArrayEquals(arrayCopy, array);
    }

    public static void assertArrayEquals(int[] expected, int[] actual) {
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
        System.out.println("All tests done.");
    }
}
