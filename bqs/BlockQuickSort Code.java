import java.util.Arrays;
import java.util.Comparator;
import java.util.Random;

public class BlockQuickSort {

    private static final int BLOCKSIZE = 128;
    private static final int IS_THRESH = 16;
    private static final int STACK_SIZE = 80;

    public static <T> void swap(T[] array, int i, int j) {
        T temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }

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
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexL[numLeft] = j;
                    numLeft += comparator.compare(array[begin + j], pivot) >= 0 ? 1 : 0;
                }
            }
            if (numRight == 0) {
                startRight = 0;
                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexR[numRight] = j;
                    numRight += comparator.compare(pivot, array[last - j]) >= 0 ? 1 : 0;
                }
            }

            num = Math.min(numLeft, numRight);
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
            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += comparator.compare(array[begin + j], pivot) >= 0 ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;
            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += comparator.compare(pivot, array[last - j]) >= 0 ? 1 : 0;
            }
        }

        num = Math.min(numLeft, numRight);
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

            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }
            while (lowerI >= startLeft) {
                swap(array, begin + upper--, begin + indexL[lowerI--]);
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }
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

    public static <T> void sortPair(int i1, int i2, T[] array, Comparator<T> comparator) {
        boolean smaller = comparator.compare(array[i2], array[i1]) < 0;
        T temp = smaller ? array[i1] : array[i2];
        array[i1] = smaller ? array[i2] : array[i1];
        array[i2] = smaller ? temp : array[i2];
    }

    public static <T> int medianOf3(T[] array, int begin, int end, Comparator<T> comparator) {
        int mid = begin + ((end - begin) / 2);
        sortPair(begin, mid, array, comparator);
        sortPair(mid, end - 1, array, comparator);
        sortPair(begin, mid, array, comparator);
        return mid;
    }

    public static <T> int partition(T[] array, int begin, int end, Comparator<T> comparator) {
        int mid = medianOf3(array, begin, end, comparator);
        return hoareBlockPartitionSimple(array, begin + 1, end - 1, mid, comparator);
    }

    public static <T> void quickSort(T[] array, int begin, int end, Comparator<T> comparator) {
        int[] stack = new int[STACK_SIZE];
        int top = 0;
        int depth = 0;
        int depthLimit = (int) (2 * Math.log(end - begin) / Math.log(2)) + 3;

        stack[top++] = begin;
        stack[top++] = end;

        do {
            end = stack[--top];
            begin = stack[--top];

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
