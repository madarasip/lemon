/* -*- mode: C++; indent-tabs-mode: nil; -*-
 *
 * This file is a part of LEMON, a generic C++ optimization library.
 *
 * Copyright (C) 2003-2009
 * Egervary Jeno Kombinatorikus Optimalizalasi Kutatocsoport
 * (Egervary Research Group on Combinatorial Optimization, EGRES).
 *
 * Permission to use, modify and distribute this software is granted
 * provided that this copyright notice appears in all copies. For
 * precise terms see the accompanying LICENSE file.
 *
 * This software is provided "AS IS" with no warranty of any kind,
 * express or implied, and with no claim as to its suitability for any
 * purpose.
 *
 */

#ifndef LEMON_RADIX_HEAP_H
#define LEMON_RADIX_HEAP_H

///\ingroup heaps
///\file
///\brief Radix heap implementation.

#include <limits>
#include <vector>

#include <lemon/error.h>

namespace lemon {

  /// \ingroup heaps
  ///
  /// \brief Radix heap data structure.
  ///
  /// This class implements the \e radix \e heap data structure.
  /// It practically conforms to the \ref concepts::Heap "heap concept",
  /// but it has some limitations due its special implementation.
  /// The type of the priorities must be \c int and the priority of an
  /// item cannot be decreased under the priority of the last removed item.
  ///
  /// \tparam IM A read-writable item map with \c int values, used
  /// internally to handle the cross references.
  template <typename IM>
  class RadixHeap {

  public:
    /// Type of the item-int map.
    typedef IM ItemIntMap;
    /// Type of the priorities.
    typedef int Prio;
    /// Type of the items stored in the heap.
    typedef typename ItemIntMap::Key Item;

    /// \brief Exception thrown by RadixHeap.
    ///
    /// This exception is thrown when an item is inserted into a
    /// RadixHeap with a priority smaller than the last erased one.
    /// \see RadixHeap
    class PriorityUnderflowError : public Exception {
    public:
      virtual const char* what() const throw() {
        return "lemon::RadixHeap::PriorityUnderflowError";
      }
    };

    /// \brief Type to represent the states of the items.
    ///
    /// Each item has a state associated to it. It can be "in heap",
    /// "pre-heap" or "post-heap". The latter two are indifferent from the
    /// heap's point of view, but may be useful to the user.
    ///
    /// The item-int map must be initialized in such way that it assigns
    /// \c PRE_HEAP (<tt>-1</tt>) to any element to be put in the heap.
    enum State {
      IN_HEAP = 0,    ///< = 0.
      PRE_HEAP = -1,  ///< = -1.
      POST_HEAP = -2  ///< = -2.
    };

  private:
    struct RadixItem {
      int prev, next, box;
      Item item;
      int prio;
      RadixItem(Item _item, int _prio) : item(_item), prio(_prio) {}
    };

    std::vector<RadixItem> _data;
    std::vector<int> _boxes;  // first element of the box
    std::vector<int> _bounds; // box[i] contains elements from
    // _bounds[i] + 1 to _bounds[i + 1]

    ItemIntMap &_iim;

    void initBounds(int minimum, int capacity) {
      if (minimum == std::numeric_limits<int>::min()) {
        throw PriorityUnderflowError();
      }

      std::vector<int> bounds;
      bounds.push_back(minimum - 1);
      bounds.push_back(minimum);

      long long cap = 2;
      const long long int_max = std::numeric_limits<int>::max();
      while (bounds.back() < capacity) {
        long long next = static_cast<long long>(minimum) + cap - 1;
        if (next <= bounds.back() || next >= int_max) {
          bounds.push_back(std::numeric_limits<int>::max());
          break;
        }
        bounds.push_back(static_cast<int>(next));
        cap *= 2;
      }

      if (bounds.back() != std::numeric_limits<int>::max()) {
        bounds.push_back(std::numeric_limits<int>::max());
      }

      std::vector<int> boxes(bounds.size() - 1, -1);
      _bounds.swap(bounds);
      _boxes.swap(boxes);
    }

  public:
    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param map A map that assigns \c int values to the items.
    /// It is used internally to handle the cross references.
    /// The assigned value must be \c PRE_HEAP (<tt>-1</tt>) for each item.
    /// \param minimum The initial minimum value of the heap. It must be
    /// greater than \c std::numeric_limits<int>::min().
    /// \param capacity The initial capacity of the heap.
    /// \warning This constructor may throw a \c PriorityUnderflowError if
    /// \c minimum is \c std::numeric_limits<int>::min().
    RadixHeap(ItemIntMap &map, int minimum = 0, int capacity = 0)
      : _iim(map)
    {
      initBounds(minimum, capacity);
    }

    /// \brief The number of items stored in the heap.
    ///
    /// This function returns the number of items stored in the heap.
    int size() const { return _data.size(); }

    /// \brief Check if the heap is empty.
    ///
    /// This function returns \c true if the heap is empty.
    bool empty() const { return _data.empty(); }

    /// \brief Make the heap empty.
    ///
    /// This functon makes the heap empty.
    /// It does not change the cross reference map. If you want to reuse
    /// a heap that is not surely empty, you should first clear it and
    /// then you should set the cross reference map to \c PRE_HEAP
    /// for each item.
    /// \param minimum The minimum value of the heap. It must be greater
    /// than \c std::numeric_limits<int>::min().
    /// \param capacity The capacity of the heap.
    /// \warning This method may throw a \c PriorityUnderflowError if
    /// \c minimum is \c std::numeric_limits<int>::min().
    void clear(int minimum = 0, int capacity = 0) {
      initBounds(minimum, capacity);
      _data.clear();
    }

  private:
    // Remove item from the box list
    void remove(int index) {
      if (_data[index].prev >= 0) {
        _data[_data[index].prev].next = _data[index].next;
      } else {
        _boxes[_data[index].box] = _data[index].next;
      }
      if (_data[index].next >= 0) {
        _data[_data[index].next].prev = _data[index].prev;
      }
    }

    // Insert item into the box list
    void insert(int box, int index) {
      if (_boxes[box] == -1) { // if the box is empty
        _boxes[box] = index;
        _data[index].next = _data[index].prev = -1;
      } else {
        _data[index].next = _boxes[box];
        _data[_boxes[box]].prev = index;
        _data[index].prev = -1;
        _boxes[box] = index;
      }
      _data[index].box = box;
    }

    // Move an item up into the proper box (for set and increase)
    void bubbleUp(int index, int pr) {
      if (_bounds[_data[index].box + 1] >= pr) {
        _data[index].prio = pr;
        return;
      }
      int box = findUp(_data[index].box + 1, pr);
      _data[index].prio = pr;
      remove(index);
      insert(box, index);
    }

    // Find up the proper box for the item with the given priority
    int findUp(int start, int pr) const {
      while (_bounds[start + 1] < pr) {
        ++start;
      }
      return start;
    }

    // Move an item down into the proper box (for set and decrease)
    void bubbleDown(int index, int pr) {
      if (_bounds[_data[index].box] < pr) {
        _data[index].prio = pr;
        return;
      }
      if (_data[index].box == 0) throw PriorityUnderflowError();
      int box = findDown(_data[index].box - 1, pr);
      _data[index].prio = pr;
      remove(index);
      insert(box, index);
    }

    // Find down the proper box for the item with the given priority
    int findDown(int start, int pr) const {
      while (start >= 0 && _bounds[start] >= pr) {
        --start;
      }
      if (start < 0) throw PriorityUnderflowError();
      return start;
    }

    // Find the first non-empty box
    int findFirst() const {
      int first = 0;
      while (_boxes[first] == -1) ++first;
      return first;
    }

    // Gives back the index of an item with minimum priority in the given box
    int minIndex(int box) const {
      int min = _boxes[box];
      for (int k = _data[min].next; k != -1; k = _data[k].next) {
        if (_data[k].prio < _data[min].prio) min = k;
      }
      return min;
    }

    // Gives back the minimum priority of the given box
    int minValue(int box) const {
      return _data[minIndex(box)].prio;
    }

    // Rearrange the items of the heap and make the first box non-empty
    void moveDown() {
      int box = findFirst();
      if (box == 0) return;
      int min = minValue(box);

      _bounds[0] = min - 1;
      _bounds[1] = min;
      int i = 2;
      long long new_bound = static_cast<long long>(min) + 1;
      while (new_bound < _bounds[box + 1] && i <= box) {
        _bounds[i] = static_cast<int>(new_bound);
        ++i;
        long long step = 1LL << (i - 2);
        new_bound = static_cast<long long>(_bounds[i - 1]) + step;
        if (new_bound > std::numeric_limits<int>::max()) {
          new_bound = std::numeric_limits<int>::max();
        }
      }
      for (; i <= box; ++i) {
        _bounds[i] = _bounds[box + 1];
      }

      int curr = _boxes[box];
      int next;
      while (curr != -1) {
        next = _data[curr].next;
        bubbleDown(curr, _data[curr].prio);
        curr = next;
      }
    }

    // Remove the index from _data
    void relocateLast(int index) {
      if (index != int(_data.size()) - 1) {
        _data[index] = _data.back();
        if (_data[index].prev != -1) {
          _data[_data[index].prev].next = index;
        } else {
          _boxes[_data[index].box] = index;
        }
        if (_data[index].next != -1) {
          _data[_data[index].next].prev = index;
        }
        _iim[_data[index].item] = index;
      }
      _data.pop_back();
    }

  public:
    /// \brief Insert an item into the heap with the given priority.
    ///
    /// This function inserts the given item into the heap with the
    /// given priority.
    /// \param i The item to insert.
    /// \param p The priority of the item.
    /// \pre \e i must not be stored in the heap.
    /// \warning This method may throw an \c PriorityUnderflowError.
    void push(const Item &i, const Prio &p) {
      int box = findDown(static_cast<int>(_boxes.size()) - 1, p);
      int n = static_cast<int>(_data.size());
      _data.push_back(RadixItem(i, p));
      try {
        _iim.set(i, n);
      } catch (...) {
        _data.pop_back();
        throw;
      }
      insert(box, n);
    }

    /// \brief Return the item having minimum priority.
    ///
    /// This function returns the item having minimum priority.
    /// \pre The heap must be non-empty.
    Item top() const {
      int box = findFirst();
      return _data[minIndex(box)].item;
    }

    /// \brief The minimum priority.
    ///
    /// This function returns the minimum priority.
    /// \pre The heap must be non-empty.
    Prio prio() const {
      int box = findFirst();
      return _data[minIndex(box)].prio;
    }

    /// \brief Remove the item having minimum priority.
    ///
    /// This function removes the item having minimum priority.
    /// \pre The heap must be non-empty.
    void pop() {
      moveDown();
      int index = _boxes[0];
      _iim[_data[index].item] = POST_HEAP;
      remove(index);
      relocateLast(index);
    }

    /// \brief Remove the given item from the heap.
    ///
    /// This function removes the given item from the heap if it is
    /// already stored.
    /// \param i The item to delete.
    /// \pre \e i must be in the heap.
    void erase(const Item &i) {
      int index = _iim[i];
      _iim[i] = POST_HEAP;
      remove(index);
      relocateLast(index);
    }

    /// \brief The priority of the given item.
    ///
    /// This function returns the priority of the given item.
    /// \param i The item.
    /// \pre \e i must be in the heap.
    Prio operator[](const Item &i) const {
      int idx = _iim[i];
      return _data[idx].prio;
    }

    /// \brief Set the priority of an item or insert it, if it is
    /// not stored in the heap.
    ///
    /// This method sets the priority of the given item if it is
    /// already stored in the heap. Otherwise it inserts the given
    /// item into the heap with the given priority.
    /// \param i The item.
    /// \param p The priority.
    /// \warning This method may throw an \c PriorityUnderflowError.
    void set(const Item &i, const Prio &p) {
      int idx = _iim[i];
      if( idx < 0 ) {
        push(i, p);
      }
      else if( p >= _data[idx].prio ) {
        bubbleUp(idx, p);
      } else {
        bubbleDown(idx, p);
      }
    }

    /// \brief Decrease the priority of an item to the given value.
    ///
    /// This function decreases the priority of an item to the given value.
    /// \param i The item.
    /// \param p The priority.
    /// \pre \e i must be stored in the heap with priority at least \e p.
    /// \warning This method may throw an \c PriorityUnderflowError.
    void decrease(const Item &i, const Prio &p) {
      int idx = _iim[i];
      bubbleDown(idx, p);
    }

    /// \brief Increase the priority of an item to the given value.
    ///
    /// This function increases the priority of an item to the given value.
    /// \param i The item.
    /// \param p The priority.
    /// \pre \e i must be stored in the heap with priority at most \e p.
    void increase(const Item &i, const Prio &p) {
      int idx = _iim[i];
      bubbleUp(idx, p);
    }

    /// \brief Return the state of an item.
    ///
    /// This method returns \c PRE_HEAP if the given item has never
    /// been in the heap, \c IN_HEAP if it is in the heap at the moment,
    /// and \c POST_HEAP otherwise.
    /// In the latter case it is possible that the item will get back
    /// to the heap again.
    /// \param i The item.
    State state(const Item &i) const {
      int s = _iim[i];
      if( s >= 0 ) s = 0;
      return State(s);
    }

    /// \brief Set the state of an item in the heap.
    ///
    /// This function sets the state of the given item in the heap.
    /// It can be used to manually clear the heap when it is important
    /// to achive better time complexity.
    /// \param i The item.
    /// \param st The state. It should not be \c IN_HEAP.
    void state(const Item& i, State st) {
      switch (st) {
      case POST_HEAP:
      case PRE_HEAP:
        if (state(i) == IN_HEAP) {
          erase(i);
        }
        _iim[i] = st;
        break;
      case IN_HEAP:
        break;
      }
    }

  }; // class RadixHeap

} // namespace lemon

#endif // LEMON_RADIX_HEAP_H
