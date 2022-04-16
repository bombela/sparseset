//! A sparse set.

use std::ops::{Deref, DerefMut};
use std::slice;

/// An implementation of a sparse set.
///
/// A sparse set is a specialized data structure for representing a set of integers.
/// It can be useful in some very narrow and specific cases, namely when the universe of possible
/// values is very large but used very sparingly and the set is iterated often or cleared often.
///
/// In this implement the SparseSet can hold an arbitrary value for every integer (key) in the set.
///
/// # Example
///
/// ```
/// use sparseset::SparseSet;
/// let mut set = SparseSet::with_capacity(128);
/// set.insert(42, 3);
/// set.insert(77, 5);
/// set.insert(23, 8);
///
/// assert_eq!(*set.get(42).unwrap(), 3);
///
/// set.remove(42);
/// assert!(!set.get(42).is_some());
///
/// for entry in set {
///     println!("- {} => {}", entry.key(), entry.value);
/// }
/// ```
///
/// # Performance
///
/// Note that SparseSet is *incredibly* inefficient in terms of space. The O(1) insertion time
/// assumes space for the element is already allocated.  Otherwise, a large key may require a
/// massive reallocation, with no direct relation to the number of elements in the collection.
/// SparseSet should only be seriously considered for small keys.
///
/// ## Runtime complexity
///
/// See how the runtime complexity of SparseSet compares to Hash and Btree maps:
///
/// |           | get       | insert   | remove   | iterate | clear        |
/// |-----------|-----------|----------|----------|---------|--------------|
/// | SparseSet | O(1)      | O(1)*    | O(1)     | O(n)    | O(1) / O(n)* |
/// | HashMap   | O(1)~     | O(1)~*   | O(1)~    | N/A     | N/A          |
/// | BTreeMap  | O(log n)  | O(log n) | O(log n) | N/A     | N/A          |
///
/// * Clear is O(1) on simple types and O(n) on types whom implements Drop.
/// * Iterating is really efficient, its iterating over a dense array. In fact, its even possible
/// to get an (even mutable) slice of the entries in the set.
///
/// See http://research.swtch.com/sparse for more details.
pub struct SparseSet<T> {
    dense: Vec<Entry<T>>,
    sparse: Vec<usize>,
}

/// An entry in the sparse set.
/// You can retrieve a slice (possibly mutable) of [Entry] from the SparseSet.
pub struct Entry<T> {
    key: usize,

    /// The value stored in the entry. A reference to it is returned by value() and value_mut(), as
    /// well as get() and get_mut() directly from SparseSet. The field can be used without going
    /// trough the accessors functions since it is public.
    pub value: T,
}

impl<T> Entry<T> {
    /// Read-only access to the entry's key.
    pub fn key(&self) -> usize {
        self.key
    }

    /// Returns the value. Mainly for symmetry with key() since the value is public anyway.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Returns the value, mutable. Mainly for symmetry with key() since the value is public
    /// anyway.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T> SparseSet<T> {
    /// Creates a SparseSet with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        let mut sparse = Vec::with_capacity(size);
        unsafe { sparse.set_len(size) }
        SparseSet {
            dense: Vec::with_capacity(size),
            sparse: sparse,
        }
    }

    pub fn len(&self) -> usize {
        self.dense.len()
    }
    pub fn capacity(&self) -> usize {
        self.sparse.len()
    }

    /// Clears the SparseSet in O(1) for simple T and O(n) if T implements Drop.
    pub fn clear(&mut self) {
        self.dense.clear();
    }

    fn dense_idx(&self, key: usize) -> Option<usize> {
        let dense_idx = self.sparse[key];
        if dense_idx < self.len() {
            let entry = &self.dense[dense_idx];
            if entry.key == key {
                return Some(dense_idx);
            }
        }
        None
    }

    /// Returns a reference to the value corresponding to the given key in O(1).
    pub fn get(&self, key: usize) -> Option<&T> {
        if let Some(dense_idx) = self.dense_idx(key) {
            Some(&self.dense[dense_idx].value)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the given key in O(1).
    pub fn get_mut(&mut self, key: usize) -> Option<&mut T> {
        if let Some(dense_idx) = self.dense_idx(key) {
            Some(&mut self.dense[dense_idx].value)
        } else {
            None
        }
    }

    /// Test if the given key is contained in the set in O(1).
    pub fn contains(&self, key: usize) -> bool {
        self.dense_idx(key).is_some()
    }

    /// Insert in the set a value for the given key in O(1).
    ///
    /// * returns true if the key was set.
    /// * returns false if the key was already set.
    ///
    /// If the key was already set, the previous value is overridden.
    pub fn insert(&mut self, key: usize, value: T) -> bool {
        assert!(
            key < self.capacity(),
            "key ({}) must be under capacity ({})",
            key,
            self.capacity()
        );
        if let Some(stored_value) = self.get_mut(key) {
            *stored_value = value;
            return false;
        }
        let n = self.dense.len();
        self.dense.push(Entry {
            key: key,
            value: value,
        });
        self.sparse[key] = n;
        true
    }

    /// Removes the given key in O(1).
    /// Returns the removed value or None if key not found.
    pub fn remove(&mut self, key: usize) -> Option<T> {
        if self.contains(key) {
            let dense_idx = self.sparse[key];
            let r = self.dense.swap_remove(dense_idx).value;
            if dense_idx < self.len() {
                let swapped_entry = &self.dense[dense_idx];
                self.sparse[swapped_entry.key] = dense_idx;
            }
            // not strictly necessary, just nice to
            // restrict any future contains(key) to one test.
            self.sparse[key] = self.capacity();
            Some(r)
        } else {
            None
        }
    }
}

/// Deref to a slice.
impl<T> Deref for SparseSet<T> {
    type Target = [Entry<T>];

    fn deref(&self) -> &Self::Target {
        &self.dense[..]
    }
}

/// Deref to a mutable slice.
impl<T> DerefMut for SparseSet<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.dense[..]
    }
}

/// Move into an interator, consuming the SparseSet.
impl<T> IntoIterator for SparseSet<T> {
    type Item = Entry<T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.dense.into_iter()
    }
}

/// An interator over the elements of the SparseSet.
impl<'a, T> IntoIterator for &'a SparseSet<T> {
    type Item = &'a Entry<T>;
    type IntoIter = slice::Iter<'a, Entry<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An interator over mutable elements of the SparseSet.
impl<'a, T> IntoIterator for &'a mut SparseSet<T> {
    type Item = &'a mut Entry<T>;
    type IntoIter = slice::IterMut<'a, Entry<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[test]
fn create() {
    let s = SparseSet::<()>::with_capacity(42);
    assert_eq!(s.len(), 0);
    assert_eq!(s.capacity(), 42);
}

#[test]
fn insert() {
    let mut s = SparseSet::with_capacity(42);
    s.insert(3, ());
    assert_eq!(s.len(), 1);
    assert_eq!(s.capacity(), 42);
    s.insert(3, ());
    assert_eq!(s.len(), 1);
    assert_eq!(s.capacity(), 42);
}

#[test]
fn clear() {
    let mut s = SparseSet::with_capacity(42);
    s.insert(3, ());
    assert_eq!(s.len(), 1);
    assert_eq!(s.capacity(), 42);
    s.clear();
    assert_eq!(s.len(), 0);
    assert_eq!(s.capacity(), 42);
}

#[test]
fn contains() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(3, ());
    s.insert(1, ());
    assert_eq!(s.len(), 2);
    assert_eq!(s.capacity(), 5);

    assert!(s.contains(0) == false);
    assert!(s.contains(1) == true);
    assert!(s.contains(2) == false);
    assert!(s.contains(3) == true);
    assert!(s.contains(4) == false);
}

#[test]
fn remove() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(3, ());
    s.insert(1, ());
    assert_eq!(s.len(), 2);
    assert_eq!(s.capacity(), 5);

    assert!(s.contains(1));
    assert!(s.contains(3));

    s.remove(3);
    assert_eq!(s.len(), 1);
    assert_eq!(s.capacity(), 5);

    assert!(s.contains(1));
    assert!(s.contains(3) == false);

    s.remove(3);
    assert_eq!(s.len(), 1);
    assert_eq!(s.capacity(), 5);

    s.remove(1);
    assert_eq!(s.len(), 0);
    assert_eq!(s.capacity(), 5);

    assert!(s.contains(1) == false);
    assert!(s.contains(3) == false);
}

#[test]
fn remove2() {
    let mut s = SparseSet::with_capacity(20_000);

    for i in 1..=10_000 {
        s.insert(i, 42);
    }

    for i in 1..=10_000 {
        s.remove(i);
    }
}

#[test]
fn remove3() {
    let mut s = SparseSet::with_capacity(100);
    s.insert(3, 42);
    s.insert(2, 42);
    s.insert(1, 42);

    s.remove(3);
    s.remove(2);
    s.remove(1);
}

#[test]
fn iter() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(3, ());
    s.insert(1, ());
    s.insert(2, ());
    s.remove(1);
    assert_eq!(s.len(), 2);

    let mut i = 0;
    let mut total = 0;
    for entry in &s {
        i += 1;
        total += entry.key();
    }
    assert_eq!(i, 2);
    assert_eq!(total, 5);
    assert_eq!(s.len(), 2);
}

#[test]
fn iter_mut() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(1, 11);
    s.insert(2, 22);
    s.remove(1);
    s.insert(4, 44);
    assert_eq!(s.len(), 2);

    let mut i = 0;
    let mut total = 0;
    for entry in &mut s {
        i += 1;
        total += entry.value;
        entry.value += 1;
    }
    assert_eq!(i, 2);
    assert_eq!(total, 22 + 44);

    let mut i = 0;
    let mut total = 0;
    for entry in &s {
        i += 1;
        total += entry.value;
    }
    assert_eq!(i, 2);
    assert_eq!(total, 23 + 45);
}

#[test]
fn into_iter() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(3, ());
    s.insert(1, ());
    s.insert(2, ());
    assert_eq!(s.len(), 3);

    let mut i = 0;
    let mut total = 0;
    for entry in s {
        i += 1;
        total += entry.key();
    }
    assert_eq!(i, 3);
    assert_eq!(total, 3 + 1 + 2);
}

#[test]
fn slice() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(3, ());
    s.insert(1, ());
    s.insert(2, ());

    {
        let the_slice: &[Entry<()>] = &s;
        let mut i = 0;
        let mut total: usize = 0;
        for entry in the_slice {
            i += 1;
            total += entry.key();
        }
        assert_eq!(i, 3);
        assert_eq!(total, 3 + 1 + 2);
    }

    s.insert(0, ());

    {
        let the_slice: &mut [Entry<()>] = &mut s;
        let mut i = 0;
        let mut total: usize = 0;
        for entry in the_slice {
            i += 1;
            total += entry.key();
            entry.value = ();
        }
        assert_eq!(i, 4);
        assert_eq!(total, 3 + 1 + 2);
    }
}

#[test]
fn get() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(1, 11);
    s.insert(2, 22);
    {
        let v = s.get(2);
        assert!(v.is_some());
        let g = s.get(1);
        assert!(g.is_some());
    }
    {
        let v = s.get_mut(2);
        assert!(v.is_some());
        let v = v.unwrap();
        *v += 1;
    }
    assert_eq!(*s.get(1).unwrap(), 11);
    assert_eq!(*s.get(2).unwrap(), 23);
}

#[test]
fn slice_indexing() {
    let mut s = SparseSet::with_capacity(5);
    s.insert(2, ());
    s.insert(1, ());
    let e = &s[0];
    assert_eq!(e.key(), 2);
}
