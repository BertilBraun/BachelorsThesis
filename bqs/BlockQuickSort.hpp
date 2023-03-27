
#pragma once
#include <assert.h>
#include <stdlib.h>

#include <algorithm>
#include <cmath>
#include <ctime>
#include <fstream>
#include <functional>
#include <iostream>
#include <queue>
#include <string>
#include <vector>

#ifndef BLOCKSIZE
#define BLOCKSIZE 128
#endif
#ifndef PIVOTSAMPLESIZE
#define PIVOTSAMPLESIZE 23
#endif
#ifndef MO3_THRESH
#define MO3_THRESH (PIVOTSAMPLESIZE * PIVOTSAMPLESIZE)
#endif

template <typename iter, typename Compare>
inline iter hoare_block_partition_simple(iter begin, iter end,
                                         iter pivot_position, Compare less) {
    typedef typename std::iterator_traits<iter>::difference_type index;
    index indexL[BLOCKSIZE], indexR[BLOCKSIZE];

    iter last = end - 1;
    std::iter_swap(pivot_position, last);
    const typename std::iterator_traits<iter>::value_type& pivot = *last;
    pivot_position = last;
    last--;

    int num_left = 0;
    int num_right = 0;
    int start_left = 0;
    int start_right = 0;
    int num;
    // main loop
    while (last - begin + 1 > 2 * BLOCKSIZE) {
        // Compare and store in buffers
        if (num_left == 0) {
            start_left = 0;
            for (index j = 0; j < BLOCKSIZE; j++) {
                indexL[num_left] = j;
                num_left += (!(less(begin[j], pivot)));
            }
        }
        if (num_right == 0) {
            start_right = 0;
            for (index j = 0; j < BLOCKSIZE; j++) {
                indexR[num_right] = j;
                num_right += !(less(pivot, *(last - j)));
            }
        }
        // rearrange elements
        num = std::min(num_left, num_right);
        for (int j = 0; j < num; j++)
            std::iter_swap(begin + indexL[start_left + j],
                           last - indexR[start_right + j]);

        num_left -= num;
        num_right -= num;
        start_left += num;
        start_right += num;
        begin += (num_left == 0) ? BLOCKSIZE : 0;
        last -= (num_right == 0) ? BLOCKSIZE : 0;

    }  // end main loop

    // Compare and store in buffers final iteration
    index shiftR = 0, shiftL = 0;
    if (num_right == 0 &&
        num_left == 0) {  // for small arrays or in the unlikely case that both
                          // buffers are empty
        shiftL = ((last - begin) + 1) / 2;
        shiftR = (last - begin) + 1 - shiftL;
        assert(shiftL >= 0);
        assert(shiftL <= BLOCKSIZE);
        assert(shiftR >= 0);
        assert(shiftR <= BLOCKSIZE);
        start_left = 0;
        start_right = 0;
        for (index j = 0; j < shiftL; j++) {
            indexL[num_left] = j;
            num_left += (!less(begin[j], pivot));
            indexR[num_right] = j;
            num_right += !less(pivot, *(last - j));
        }
        if (shiftL < shiftR) {
            assert(shiftL + 1 == shiftR);
            indexR[num_right] = shiftR - 1;
            num_right += !less(pivot, *(last - shiftR + 1));
        }
    } else if (num_right != 0) {
        shiftL = (last - begin) - BLOCKSIZE + 1;
        shiftR = BLOCKSIZE;
        assert(shiftL >= 0);
        assert(shiftL <= BLOCKSIZE);
        assert(num_left == 0);
        start_left = 0;
        for (index j = 0; j < shiftL; j++) {
            indexL[num_left] = j;
            num_left += (!less(begin[j], pivot));
        }
    } else {
        shiftL = BLOCKSIZE;
        shiftR = (last - begin) - BLOCKSIZE + 1;
        assert(shiftR >= 0);
        assert(shiftR <= BLOCKSIZE);
        assert(num_right == 0);
        start_right = 0;
        for (index j = 0; j < shiftR; j++) {
            indexR[num_right] = j;
            num_right += !(less(pivot, *(last - j)));
        }
    }

    // rearrange final iteration
    num = std::min(num_left, num_right);
    for (int j = 0; j < num; j++)
        std::iter_swap(begin + indexL[start_left + j],
                       last - indexR[start_right + j]);

    num_left -= num;
    num_right -= num;
    start_left += num;
    start_right += num;
    begin += (num_left == 0) ? shiftL : 0;
    last -= (num_right == 0) ? shiftR : 0;
    // end final iteration

    // rearrange elements remaining in buffer
    if (num_left != 0) {
        assert(num_right == 0);
        int lowerI = start_left + num_left - 1;
        index upper = last - begin;
        // search first element to be swapped
        while (lowerI >= start_left && indexL[lowerI] == upper) {
            upper--;
            lowerI--;
        }
        while (lowerI >= start_left)
            std::iter_swap(begin + upper--, begin + indexL[lowerI--]);

        std::iter_swap(pivot_position, begin + upper + 1);  // fetch the pivot
        return begin + upper + 1;
    } else if (num_right != 0) {
        assert(num_left == 0);
        int lowerI = start_right + num_right - 1;
        index upper = last - begin;
        // search first element to be swapped
        while (lowerI >= start_right && indexR[lowerI] == upper) {
            upper--;
            lowerI--;
        }

        while (lowerI >= start_right)
            std::iter_swap(last - upper--, last - indexR[lowerI--]);

        std::iter_swap(pivot_position, last - upper);  // fetch the pivot
        return last - upper;
    } else {  // no remaining elements
        assert(last + 1 == begin);
        std::iter_swap(pivot_position, begin);  // fetch the pivot
        return begin;
    }
}

template <typename iter, typename Compare>
inline void sort_pair(iter i1, iter i2, Compare less) {
    typedef typename std::iterator_traits<iter>::value_type T;
    bool smaller = less(*i2, *i1);
    T temp = std::move(smaller ? *i1 : temp);
    *i1 = std::move(smaller ? *i2 : *i1);
    *i2 = std::move(smaller ? temp : *i2);
}

template <typename iter, typename Compare>
inline iter median_of_3(iter begin, iter end, Compare less) {
    iter mid = begin + ((end - begin) / 2);
    sort_pair(begin, mid, less);
    sort_pair(mid, end - 1, less);
    sort_pair(begin, mid, less);
    return mid;
}

template <typename iter, typename Compare>
struct Hoare_block_partition_simple {
    static inline iter partition(iter begin, iter end, Compare less) {
        // choose pivot
        iter mid = median_of_3(begin, end, less);
        // partition
        return hoare_block_partition_simple(begin + 1, end - 1, mid, less);
    }
};

template <template <class, class> class Partitioner, typename iter,
          typename Compare>
inline void qsort(iter begin, iter end, Compare less) {
    const int depth_limit = 2 * ilogb((double)(end - begin)) + 3;
    iter stack[80];
    iter* s = stack;
    int depth_stack[40];
    int depth = 0;
    int* d_s_top = depth_stack;
    *s = begin;
    *(s + 1) = end;
    s += 2;
    *d_s_top = 0;
    ++d_s_top;
    do {
        if (depth < depth_limit && (end - begin > IS_THRESH)) {
            iter pivot;
            pivot = Partitioner<iter, Compare>::partition(begin, end, less);
            if (pivot - begin > end - pivot) {
                *s = begin;
                *(s + 1) = pivot;
                begin = pivot + 1;
            } else {
                *s = pivot + 1;
                *(s + 1) = end;
                end = pivot;
            }
            s += 2;
            depth++;
            *d_s_top = depth;
            ++d_s_top;
        } else {
            if (end - begin > IS_THRESH) {  // if recursion depth limit exceeded
                std::partial_sort(begin, end, end);
            } else
                insertionsort::insertion_sort(
                    begin, end,
                    less);  // copy of std::__insertion_sort (GCC 4.7.2)
            // pop new subarray from stack
            s -= 2;
            begin = *s;
            end = *(s + 1);
            --d_s_top;
            depth = *d_s_top;
        }
    } while (s != stack);
}

int main(void) {
    std::vector<int> v;

    // fill vector with random numbers

    qsort<Hoare_block_partition_simple>(v.begin(), v.end(), std::less<int>());
}