
import java.util.Arrays;

public class BlockQuickSortTesting {

  public static void main(String[] args) {

    if (FIND)
      for (int len = 4; len < 50; len++) {
        int array[] = new int[len];
        for (int i = 0; i < len; i++) {
          array[i] = i + 5;
        }
        for (int i = 0; i < 5000; i++) {
          // shuffle array
          for (int j = 0; j < len; j++) {
            int k = (int) (Math.random() * len);
            int tmp = array[j];
            array[j] = array[k];
            array[k] = tmp;
          }

          for (int j = 0; j < len; j++) {
            String s = Arrays.toString(array);
            if (hoareBlockPartition(array, 0, len, j) == -1000000) {
              // System.out.println("Error: " + s);
              // System.out.println(j);
            }
          }
        }
      }

    int[] array = { -1753503446, 393980209, -1753503455 };
    int res = hoareBlockPartition(array, 0, array.length, 0);
    System.out.println("hoareBlockPartition: " + res);
    System.out.println(Arrays.toString(array));
  }

  private static final int BLOCKSIZE = 2; // 128
  private static final int IS_THRESH = 3; // 16
  private static final int STACK_SIZE = 80;
  private static final int REQUIRED = 6;
  private static final boolean FIND = false;

  public static int hoareBlockPartition(
      int[] array,
      int begin,
      int end,
      int pivotPosition) {
    int[] indexL = new int[BLOCKSIZE];
    int[] indexR = new int[BLOCKSIZE];

    int last = end - 1;
    int pivot = array[pivotPosition];
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
          numLeft += array[begin + j] >= pivot ? 1 : 0;
        }
      }
      if (numRight == 0) {
        startRight = 0;
        for (int j = 0; j < BLOCKSIZE; j++) {
          indexR[numRight] = j;
          numRight += pivot >= array[last - j] ? 1 : 0;
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
        numLeft += array[begin + j] >= pivot ? 1 : 0;
        indexR[numRight] = j;
        numRight += pivot >= array[last - j] ? 1 : 0;
      }
      if (shiftL < shiftR) {
        indexR[numRight] = shiftR - 1;
        numRight += pivot >= array[last - shiftR + 1] ? 1 : 0;
      }
    } else if (numRight != 0) {
      shiftL = (last - begin) - BLOCKSIZE + 1;
      shiftR = BLOCKSIZE;
      startLeft = 0;
      for (int j = 0; j < shiftL; j++) {
        indexL[numLeft] = j;
        numLeft += array[begin + j] >= pivot ? 1 : 0;
      }
    } else {
      shiftL = BLOCKSIZE;
      shiftR = (last - begin) - BLOCKSIZE + 1;
      startRight = 0;
      for (int j = 0; j < shiftR; j++) {
        indexR[numRight] = j;
        numRight += pivot >= array[last - j] ? 1 : 0;
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

    if (numLeft > 0 || numRight > 0 || true) {
      System.out.println("--------------------");
      System.out.println("numLeft: " + numLeft);
      System.out.println("numRight: " + numRight);
      System.out.println("startLeft: " + startLeft);
      System.out.println("startRight: " + startRight);
      System.out.println("begin: " + begin);
      System.out.println("last: " + last);
      System.out.println("shiftL: " + shiftL);
      System.out.println("shiftR: " + shiftR);
      System.out.println("pivot: " + pivot);
      System.out.println("num: " + num);
      System.out.println("indexL: " + Arrays.toString(indexL));
      System.out.println("indexR: " + Arrays.toString(indexR));
      System.out.println("array: " + Arrays.toString(array));
    }
    if (numLeft != 0) {
      int lowerI = startLeft + numLeft - 1;
      int upper = last - begin;

      while (lowerI >= startLeft && indexL[lowerI] == upper) {
        StringBuilder sb = new StringBuilder();
        sb.append("Looing at: ");
        sb.append(lowerI);
        sb.append("\n");
        sb.append(" upper: ");
        sb.append(upper);
        sb.append("\n");
        sb.append(" indexL[lowerI]: ");
        sb.append(indexL[lowerI]);
        sb.append("\n");
        sb.append(" array[begin + upper]: ");
        sb.append(array[begin + upper]);
        sb.append("\n");
        sb.append(" array[begin + indexL[lowerI]]: ");
        sb.append(array[begin + indexL[lowerI]]);
        sb.append("\n");
        sb.append(" array: ");
        sb.append(Arrays.toString(array));
        sb.append("\n");
        sb.append(" indexL: ");
        sb.append(Arrays.toString(indexL));
        // System.out.println(sb.toString());
        // System.out.println("---------------------");
        upper--;
        lowerI--;
        if (lowerI >= startLeft && indexL[lowerI] != upper && false) {
          System.out.println("---------------------");
          System.out.println("lowerI: " + lowerI);
          System.out.println(" upper: " + upper);
          System.out.println(" upper calc: " + (last - begin - (startLeft + numLeft - 1 - lowerI)));
          System.out.println(" indexL[lowerI]: " + indexL[lowerI]);
          System.out.println(" array[begin + upper]: " + array[begin + upper]);
          System.out.println(" array[begin + indexL[lowerI]]: " + array[begin + indexL[lowerI]]);
          System.out.println(" array: " + Arrays.toString(array));
          System.out.println(" indexL: " + Arrays.toString(indexL));
        }
      }

      int cnt = 0;
      while (lowerI >= startLeft) {
        StringBuilder sb = new StringBuilder();
        sb.append("lowerI: ");
        sb.append(lowerI);
        sb.append("\n");
        sb.append(" upper: ");
        sb.append(upper);
        sb.append("\n");
        sb.append(" begin: ");
        sb.append(begin);
        sb.append("\n");
        sb.append(" startLeft: ");
        sb.append(startLeft);
        sb.append("\n");
        sb.append(" numLeft: ");
        sb.append(numLeft);
        sb.append("\n");
        sb.append(" indexL[lowerI]: ");
        sb.append(indexL[lowerI]);
        sb.append("\n");
        sb.append(" array[begin + upper]: ");
        sb.append(array[begin + upper]);
        sb.append("\n");
        sb.append(" array[begin + indexL[lowerI]]: ");
        sb.append(array[begin + indexL[lowerI]]);
        sb.append("\n");
        sb.append(" array: ");
        sb.append(Arrays.toString(array));
        sb.append("\n");
        // This loop iterates through the remaining elements in the indexL array starting from the current lowerI value.
        swap(array, begin + upper--, begin + indexL[lowerI--]);
        // Swaps the element at the position begin + upper with the element at the position begin + indexL[lowerI]. After swapping, both upper and lowerI are decremented.
        sb.append(" array: ");
        sb.append(Arrays.toString(array));
        sb.append("\n");
        sb.append(" indexL: ");
        sb.append(Arrays.toString(indexL));
        if (!FIND) {
          System.out.println(sb.toString());
          System.out.println("--------------------------------------------------");

        }
        cnt++;
        if (cnt > REQUIRED && FIND)
          return -1000000;
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

  public static void quickSort(int[] array, int begin, int end) {
    int[] stack = new int[STACK_SIZE];
    int top = 0;
    int depth = 0;
    int depthLimit = (int) (2 * Math.log(end - begin) / Math.log(2)) + 3;

    stack[top++] = begin;
    stack[top++] = end;

    while (top > 0) {
      end = stack[--top];
      begin = stack[--top];

      while (end - begin > IS_THRESH && depth < depthLimit) {
        int pivot = partition(array, begin, end);
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
      }

      if (end - begin <= IS_THRESH || depth >= depthLimit) {
        insertionSort(array, begin, end);
      }

      depth--;
    }
  }

  public static void quickSortRec(int[] array, int begin, int end) {
    int depth = 0;
    int depthLimit = (int) (2 * Math.log(end - begin) / Math.log(2)) + 3;
    quickSortRec(array, begin, end, depth, depthLimit);
  }

  public static void quickSortRec(int[] array, int begin, int end, int depth, int depthLimit) {

    if (end - begin <= IS_THRESH || depth >= depthLimit) {
      insertionSort(array, begin, end);
      return;
    }

    int pivot = partition(array, begin, end);
    quickSortRec(array, begin, pivot, depth + 1, depthLimit);
    quickSortRec(array, pivot + 1, end, depth + 1, depthLimit);
  }

  public static void insertionSort(int[] array, int begin, int end) {
    Arrays.sort(array, begin, end);
  }

  public static void quickSort(int[] array) {
    quickSort(array, 0, array.length);
  }

  public static void swap(int[] array, int i, int j) {
    int temp = array[i];
    array[i] = array[j];
    array[j] = temp;
  }

  public static void sortPair(int i1, int i2, int[] array) {
    if (array[i1] > array[i2]) {
      swap(array, i1, i2);
    }
  }

  public static int medianOf3(int[] array, int begin, int end) {
    int mid = begin + ((end - begin) / 2);
    sortPair(begin, mid, array);
    sortPair(mid, end - 1, array);
    sortPair(begin, mid, array);
    return mid;
  }

  public static int partition(int[] array, int begin, int end) {
    int mid = medianOf3(array, begin, end);
    return hoareBlockPartition(array, begin + 1, end - 1, mid);
  }

  public static boolean permutation(int[] array1, int[] array2, int begin, int end) {

    for (int i = begin; i < end; i++) {
      int count1 = 0;
      int count2 = 0;

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
