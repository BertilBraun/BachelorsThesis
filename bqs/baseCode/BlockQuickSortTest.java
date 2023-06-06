import java.util.Arrays;
import java.util.Random;

class BlockQuickSortTest {

    public static void main(String[] args) {
        BlockQuickSortTest.runAllTests();
    }

    public static void quickSort(int[] array) {
        BlockQuickSort.quickSort(array, 0, array.length);
    }

    public static void testQuickSortEmptyArray() {
        int[] array = new int[] {};
        quickSort(array);
        assertArrayEquals(new int[] {}, array);
    }

    public static void testQuickSortSingleElement() {
        int[] array = new int[] { 3 };
        quickSort(array);
        assertArrayEquals(new int[] { 3 }, array);
    }

    public static void testQuickSortSortedArray() {
        int[] array = new int[] { 1, 2, 3, 4, 5 };
        quickSort(array);
        assertArrayEquals(new int[] { 1, 2, 3, 4, 5 }, array);
    }

    public static void testQuickSortReverseSortedArray() {
        int[] array = new int[] { 5, 4, 3, 2, 1 };
        quickSort(array);
        assertArrayEquals(new int[] { 1, 2, 3, 4, 5 }, array);
    }

    public static void testQuickSortArrayWithDuplicates() {
        int[] array = new int[] { 3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5 };
        quickSort(array);
        assertArrayEquals(new int[] { 1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9 }, array);
    }

    public static void testQuickSortArrayWithNegativeElements() {
        int[] array = new int[] { -5, 3, -1, 2, -8, 0 };
        quickSort(array);
        assertArrayEquals(new int[] { -8, -5, -1, 0, 2, 3 }, array);
    }

    public static void testQuickSortArrayWithSameElements() {
        int[] array = new int[] { 7, 7, 7, 7, 7, 7, 7 };
        quickSort(array);
        assertArrayEquals(new int[] { 7, 7, 7, 7, 7, 7, 7 }, array);
    }

    public static void testQuickSortArrayWithRandomElements() {
        int[] array = new Random().ints(1000, 0, 10000).boxed().mapToInt(Integer::intValue).toArray();
        int[] arrayCopy = array.clone();
        quickSort(array);
        Arrays.sort(arrayCopy);
        assertArrayEquals(arrayCopy, array);
    }

    public static void testQuickSortArrayWithAllPermutations() {
        final int MAX_BOUND = 10;
        System.out.println("Testing all permutations of arrays of size up to " + MAX_BOUND);
        long startTime = System.currentTimeMillis();
        for (int bound = 1; bound <= MAX_BOUND; bound++) {
            System.out.println("Testing all permutations of arrays of size " + bound);
            int[] array = new int[bound];
            generateAndTest(array, 0);
        }
        long endTime = System.currentTimeMillis();
        System.out.println("Testing all permutations of arrays of size up to " + MAX_BOUND + " took "
                + (endTime - startTime) + " milliseconds.");
    }

    private static void generateAndTest(int[] array, int index) {
        if (index == array.length) {
            int[] arrayToTest = array.clone();
            int[] sortedArray = array.clone();
            Arrays.sort(sortedArray);
            quickSort(arrayToTest);
            assertArrayEquals(sortedArray, arrayToTest);
        } else {
            for (int i = 1; i <= array.length; i++) {
                if (index == 0)
                    System.out.println("Testing all permutations of arrays of size " + array.length + " (" + i + ")");
                array[index] = i;
                generateAndTest(array, index + 1);
            }
        }
    }

    public static void assertArrayEquals(int[] expected, int[] actual) {
        if (!Arrays.equals(expected, actual)) {
            System.out.println("expected: " + Arrays.toString(expected) + " but was: " + Arrays.toString(actual));
        }
        count++;
    }

    static int count = 0;

    public static void runAllTests() {
        testQuickSortEmptyArray();
        testQuickSortSingleElement();
        testQuickSortSortedArray();
        testQuickSortReverseSortedArray();
        testQuickSortArrayWithDuplicates();
        testQuickSortArrayWithNegativeElements();
        testQuickSortArrayWithSameElements();
        testQuickSortArrayWithRandomElements();
        testQuickSortArrayWithAllPermutations();
        System.out.println("All tests done.");
        System.out.println("Total tests: " + count);
    }
}
