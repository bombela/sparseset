# sparseset
A Sparse Set implemention in rust.

A sparse set is a specialized data structure for representing a set of integers.
It can be useful in some very narrow and specific cases, namely when the universe of possible
values is very large but used very sparingly and the set is iterated often or cleared often.

In this implementation the SparseSet can hold an arbitrary value for every integer (key) in the set.

# Use it with Cargo

```
[dependencies]
sparseset = "0.1.0"
```

# Example

```rust
use sparseset::SparseSet;
let mut set = SparseSet::with_capacity(128);
set.insert(42, 3);
set.insert(77, 5);
set.insert(23, 8);

assert_eq!(*set.get(42).unwrap(), 3);

set.remove(42);
assert!(!set.get(42).is_some());

for entry in set {
    println!("- {} => {}", entry.key(), entry.value);
}
```

# Performance

Note that SparseSet is *incredibly* inefficient in terms of space. The O(1) insertion time
assumes space for the element is already allocated.  Otherwise, a large key may require a
massive reallocation, with no direct relation to the number of elements in the collection.
SparseSet should only be seriously considered for small keys.

## Runtime complexity

See how the runtime complexity of SparseSet compares to Hash and Btree maps:

|           | get       | insert   | remove   | iterate | clear        |
|-----------|-----------|----------|----------|---------|--------------|
| SparseSet | O(1)      | O(1)*    | O(1)     | O(n)    | O(1) / O(n)* |
| HashMap   | O(1)~     | O(1)~*   | O(1)~    | N/A     | N/A          |
| BTreeMap  | O(log n)  | O(log n) | O(log n) | N/A     | N/A          |

* Clear is O(1) on simple types and O(n) on types whom implements Drop.
* Iterating is really efficient, its iterating over a dense array. In fact, its even possible
to get an (even mutable) slice of the entries in the set.

See http://research.swtch.com/sparse for more details.
