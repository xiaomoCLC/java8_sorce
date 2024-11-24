/*
 * Copyright (c) 1997, 2017, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 */

package java.util;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import sun.misc.SharedSecrets;

/**
 * Hash table based implementation of the <tt>Map</tt> interface.  This
 * implementation provides all of the optional map operations, and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  (The <tt>HashMap</tt>
 * class is roughly equivalent to <tt>Hashtable</tt>, except that it is
 * unsynchronized and permits nulls.)  This class makes no guarantees as to
 * the order of the map; in particular, it does not guarantee that the order
 * will remain constant over time.
 *
 * <p>This implementation provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the hash function
 * disperses the elements properly among the buckets.  Iteration over
 * collection views requires time proportional to the "capacity" of the
 * <tt>HashMap</tt> instance (the number of buckets) plus its size (the number
 * of key-value mappings).  Thus, it's very important not to set the initial
 * capacity too high (or the load factor too low) if iteration performance is
 * important.
 *
 * <p>An instance of <tt>HashMap</tt> has two parameters that affect its
 * performance: <i>initial capacity</i> and <i>load factor</i>.  The
 * <i>capacity</i> is the number of buckets in the hash table, and the initial
 * capacity is simply the capacity at the time the hash table is created.  The
 * <i>load factor</i> is a measure of how full the hash table is allowed to
 * get before its capacity is automatically increased.  When the number of
 * entries in the hash table exceeds the product of the load factor and the
 * current capacity, the hash table is <i>rehashed</i> (that is, internal data
 * structures are rebuilt) so that the hash table has approximately twice the
 * number of buckets.
 *
 * <p>As a general rule, the default load factor (.75) offers a good
 * tradeoff between time and space costs.  Higher values decrease the
 * space overhead but increase the lookup cost (reflected in most of
 * the operations of the <tt>HashMap</tt> class, including
 * <tt>get</tt> and <tt>put</tt>).  The expected number of entries in
 * the map and its load factor should be taken into account when
 * setting its initial capacity, so as to minimize the number of
 * rehash operations.  If the initial capacity is greater than the
 * maximum number of entries divided by the load factor, no rehash
 * operations will ever occur.
 *
 * <p>If many mappings are to be stored in a <tt>HashMap</tt>
 * instance, creating it with a sufficiently large capacity will allow
 * the mappings to be stored more efficiently than letting it perform
 * automatic rehashing as needed to grow the table.  Note that using
 * many keys with the same {@code hashCode()} is a sure way to slow
 * down performance of any hash table. To ameliorate impact, when keys
 * are {@link Comparable}, this class may use comparison order among
 * keys to help break ties.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access a hash map concurrently, and at least one of
 * the threads modifies the map structurally, it <i>must</i> be
 * synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 *
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new HashMap(...));</pre>
 *
 * <p>The iterators returned by all of this class's "collection view methods"
 * are <i>fail-fast</i>: if the map is structurally modified at any time after
 * the iterator is created, in any way except through the iterator's own
 * <tt>remove</tt> method, the iterator will throw a
 * {@link ConcurrentModificationException}.  Thus, in the face of concurrent
 * modification, the iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the
 * future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw <tt>ConcurrentModificationException</tt> on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>the fail-fast behavior of iterators
 * should be used only to detect bugs.</i>
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 * @author Doug Lea
 * @author Josh Bloch
 * @author Arthur van Hoff
 * @author Neal Gafter
 * @see Object#hashCode()
 * @see Collection
 * @see Map
 * @see TreeMap
 * @see Hashtable
 * @since 1.2
 */
public class HashMap<K, V> extends AbstractMap<K, V> implements Map<K, V>, Cloneable, Serializable {

    private static final long serialVersionUID = 362498820763181265L;

    /*
     * Implementation notes.
     *
     * This map usually acts as a binned (bucketed) hash table, but
     * when bins get too large, they are transformed into bins of
     * TreeNodes, each structured similarly to those in
     * java.util.TreeMap. Most methods try to use normal bins, but
     * relay to TreeNode methods when applicable (simply by checking
     * instanceof a node).  Bins of TreeNodes may be traversed and
     * used like any others, but additionally support faster lookup
     * when overpopulated. However, since the vast majority of bins in
     * normal use are not overpopulated, checking for existence of
     * tree bins may be delayed in the course of table methods.
     *
     * Tree bins (i.e., bins whose elements are all TreeNodes) are
     * ordered primarily by hashCode, but in the case of ties, if two
     * elements are of the same "class C implements Comparable<C>",
     * type then their compareTo method is used for ordering. (We
     * conservatively check generic types via reflection to validate
     * this -- see method comparableClassFor).  The added complexity
     * of tree bins is worthwhile in providing worst-case O(log n)
     * operations when keys either have distinct hashes or are
     * orderable, Thus, performance degrades gracefully under
     * accidental or malicious usages in which hashCode() methods
     * return values that are poorly distributed, as well as those in
     * which many keys share a hashCode, so long as they are also
     * Comparable. (If neither of these apply, we may waste about a
     * factor of two in time and space compared to taking no
     * precautions. But the only known cases stem from poor user
     * programming practices that are already so slow that this makes
     * little difference.)
     *
     * Because TreeNodes are about twice the size of regular nodes, we
     * use them only when bins contain enough nodes to warrant use
     * (see TREEIFY_THRESHOLD). And when they become too small (due to
     * removal or resizing) they are converted back to plain bins.  In
     * usages with well-distributed user hashCodes, tree bins are
     * rarely used.  Ideally, under random hashCodes, the frequency of
     * nodes in bins follows a Poisson distribution
     * (http://en.wikipedia.org/wiki/Poisson_distribution) with a
     * parameter of about 0.5 on average for the default resizing
     * threshold of 0.75, although with a large variance because of
     * resizing granularity. Ignoring variance, the expected
     * occurrences of list size k are (exp(-0.5) * pow(0.5, k) /
     * factorial(k)). The first values are:
     *
     * 0:    0.60653066
     * 1:    0.30326533
     * 2:    0.07581633
     * 3:    0.01263606
     * 4:    0.00157952
     * 5:    0.00015795
     * 6:    0.00001316
     * 7:    0.00000094
     * 8:    0.00000006
     * more: less than 1 in ten million
     *
     * The root of a tree bin is normally its first node.  However,
     * sometimes (currently only upon Iterator.remove), the root might
     * be elsewhere, but can be recovered following parent links
     * (method TreeNode.root()).
     *
     * All applicable internal methods accept a hash code as an
     * argument (as normally supplied from a public method), allowing
     * them to call each other without recomputing user hashCodes.
     * Most internal methods also accept a "tab" argument, that is
     * normally the current table, but may be a new or old one when
     * resizing or converting.
     *
     * When bin lists are treeified, split, or untreeified, we keep
     * them in the same relative access/traversal order (i.e., field
     * Node.next) to better preserve locality, and to slightly
     * simplify handling of splits and traversals that invoke
     * iterator.remove. When using comparators on insertion, to keep a
     * total ordering (or as close as is required here) across
     * rebalancings, we compare classes and identityHashCodes as
     * tie-breakers.
     *
     * The use and transitions among plain vs tree modes is
     * complicated by the existence of subclass LinkedHashMap. See
     * below for hook methods defined to be invoked upon insertion,
     * removal and access that allow LinkedHashMap internals to
     * otherwise remain independent of these mechanics. (This also
     * requires that a map instance be passed to some utility methods
     * that may create new nodes.)
     *
     * The concurrent-programming-like SSA-based coding style helps
     * avoid aliasing errors amid all of the twisty pointer operations.
     */

    /**
     * The default initial capacity - MUST be a power of two.
     */
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<30.
     */
    static final int MAXIMUM_CAPACITY = 1 << 30;

    /**
     * The load factor used when none specified in constructor.
     */
    static final float DEFAULT_LOAD_FACTOR = 0.75f;

    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2 and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     *
     * 树化阈值
     */
    static final int TREEIFY_THRESHOLD = 8;

    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     */
    static final int UNTREEIFY_THRESHOLD = 6;

    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * Should be at least 4 * TREEIFY_THRESHOLD to avoid conflicts
     * between resizing and treeification thresholds.
     */
    static final int MIN_TREEIFY_CAPACITY = 64;

    /**
     * Basic hash bin node, used for most entries.  (See below for
     * TreeNode subclass, and in LinkedHashMap for its Entry subclass.)
     */
    static class Node<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        V value;
        Node<K, V> next;    //【链表】后指针

        Node(int hash, K key, V value, Node<K, V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey() {
            return key;
        }

        public final V getValue() {
            return value;
        }

        public final String toString() {
            return key + "=" + value;
        }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this) {
                return true;
            }
            if (o instanceof Map.Entry) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                if (Objects.equals(key, e.getKey()) &&
                        Objects.equals(value, e.getValue())) {
                    return true;
                }
            }
            return false;
        }
    }

    /* ---------------- Static utilities -------------- */

    /**
     * 通过扰动函数，重新计算hashCode的值
     */
    // egx: key="k1"
    // eg1: key=0
    static final int hash(Object key) {
        int h;
        /**
         * 按位异或运算（^）：两个数转为二进制，然后从高位开始比较，如果相同则为0，不相同则为1。
         *
         * 扰动函数————(h = key.hashCode()) ^ (h >>> 16) 表示：
         * 将key的hashCode一分为二。其中：
         *  【高半区16位】数据不变。
         *  【低半区16位】数据与高半区16位数据进行异或操作，以此来加大低位的随机性。
         * 注意：如果key的哈希code小于等于16位，那么是没有任何影响的。只有大于16位，才会触发扰动函数的执行效果。
         */
        // egx: 110100100110^000000000000=110100100110，由于k1的hashCode都是在低16位，所以原样返回3366
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }

    /**
     * 如果x的类Class是"class C implements Comparable<C>"的形式，则返回它的Class，否则返回null。
     */
    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c; // 表示x的类型
            Type[] ts, as;
            Type t;
            ParameterizedType p; // ParameterizedType接口，它是Type的子接口，表示参数化类型。如：List<Integer>;

            /** 1：如果x是String类型，则直接返回String类型 */
            if ((c = x.getClass()) == String.class) return c;

            /** 2：获取c所实现的接口集合 */
            if ((ts = c.getGenericInterfaces()) != null)
                for (int i = 0; i < ts.length; ++i)
                    // 举例：Map<String,Long> map
                    //      instanceof ParameterizedType=true
                    //      getActualTypeArguments()=[String, Long]
                    //      getRawType()=java.util.Map
                    /** 判断x的类Class是否是"class C implements Comparable<C>"的形式 */
                    if (((t = ts[i]) instanceof ParameterizedType) &&                                    // 判断是否是带有泛型参数的类型
                            ((p = (ParameterizedType) t).getRawType() == Comparable.class) &&            // 获得变量类型
                            (as = p.getActualTypeArguments()) != null && as.length == 1 && as[0] == c)   // 获得第1个泛型参数类型
                        return c;
        }
        return null;
    }

    /**
     * 如果x匹配kc（k筛选的可比较类），则返回k.compareTo(x)，否则为0。
     * 上层调用：compareComparables(kc, k, pk)
     *      kc = x.key.class（x：遍历的链表中的节点）
     *      k = x.key
     *      pk = p.key（p：x与其进行大小比较的红黑树中的节点）
     */
    @SuppressWarnings({"rawtypes", "unchecked"})
    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 : ((Comparable) k).compareTo(x)); // 尝试让k与x通过Comparable接口进行大小对比
    }

    /**
     * Returns a power of two size for the given target capacity.
     */
    static final int tableSizeFor(int cap) {
        int n = cap - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    /* ---------------- Fields -------------- */

    /**
     * The table, initialized on first use, and resized as
     * necessary. When allocated, length is always a power of two.
     * (We also tolerate length zero in some operations to allow
     * bootstrapping mechanics that are currently not needed.)
     */
    // 存储Node数组。
    transient Node<K, V>[] table;

    /**
     * Holds cached entrySet(). Note that AbstractMap fields are used
     * for keySet() and values().
     */
    transient Set<Map.Entry<K, V>> entrySet;

    /**
     * The number of key-value mappings contained in this map.
     */
    transient int size;

    /**
     * The number of times this HashMap has been structurally modified
     * Structural modifications are those that change the number of mappings in
     * the HashMap or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the HashMap fail-fast.  (See ConcurrentModificationException).
     */
    transient int modCount;

    /**
     * 阈值=capacity*loadFactor
     * The next size value at which to resize (capacity * load factor).
     *
     * @serial
     */
    // (The javadoc description is true upon serialization.
    // Additionally, if the table array has not been allocated, this
    // field holds the initial array capacity, or zero signifying
    // DEFAULT_INITIAL_CAPACITY.)
    int threshold;

    /**
     * 加载因子
     * The load factor for the hash table.
     */
    final float loadFactor;

    /* ---------------- Public operations -------------- */

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and load factor.
     *
     * @param initialCapacity the initial capacity
     * @param loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *                                  or the load factor is nonpositive
     */
    public HashMap(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0) {
            throw new IllegalArgumentException("Illegal initial capacity: " +
                    initialCapacity);
        }
        if (initialCapacity > MAXIMUM_CAPACITY) {
            initialCapacity = MAXIMUM_CAPACITY;
        }
        if (loadFactor <= 0 || Float.isNaN(loadFactor)) {
            throw new IllegalArgumentException("Illegal load factor: " +
                    loadFactor);
        }
        this.loadFactor = loadFactor;
        this.threshold = tableSizeFor(initialCapacity);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and the default load factor (0.75).
     *
     * @param initialCapacity the initial capacity.
     * @throws IllegalArgumentException if the initial capacity is negative.
     */
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the default initial capacity
     * (16) and the default load factor (0.75).
     */
    public HashMap() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }

    /**
     * Constructs a new <tt>HashMap</tt> with the same mappings as the
     * specified <tt>Map</tt>.  The <tt>HashMap</tt> is created with
     * default load factor (0.75) and an initial capacity sufficient to
     * hold the mappings in the specified <tt>Map</tt>.
     *
     * @param m the map whose mappings are to be placed in this map
     * @throws NullPointerException if the specified map is null
     */
    public HashMap(Map<? extends K, ? extends V> m) {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }

    /**
     * Implements Map.putAll and Map constructor.
     *
     * @param m     the map
     * @param evict false when initially constructing this map, else
     *              true (relayed to method afterNodeInsertion).
     */
    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();
        if (s > 0) {
            if (table == null) { // pre-size
                float ft = ((float) s / loadFactor) + 1.0F;
                int t = ((ft < (float) MAXIMUM_CAPACITY) ?
                                 (int) ft : MAXIMUM_CAPACITY);
                if (t > threshold) {
                    threshold = tableSizeFor(t);
                }
            } else if (s > threshold) {
                resize();
            }
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     *
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key==null ? k==null :
     * key.equals(k))}, then this method returns {@code v}; otherwise
     * it returns {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(Object, Object)
     */
    public V get(Object key) {
        Node<K, V> e;
        return (e = getNode(hash(key), key)) == null ? null : e.value;
    }

    /**
     * 在链表或红黑树中查找元素
     */
    final Node<K, V> getNode(int hash, Object key) {
        Node<K, V>[] tab;
        Node<K, V> first;
        Node<K, V> e;
        int n;
        K k;
        /** table存在元素 并且 根据hash寻址后的下标位置也有元素存在 */
        if ((tab = table) != null && (n = tab.length) > 0 && (first = tab[(n - 1) & hash]) != null) {
            /** hash值相同，并且key值也相同。真幸运，第一个元素就是待寻找的元素！！！ */
            if (first.hash == hash &&  ((k = first.key) == key || (key != null && key.equals(k)))) {
                return first;
            }
            /** 向后寻找 */
            if ((e = first.next) != null) {
                // 方式一：在红黑树结构里寻找
                if (first instanceof TreeNode) {
                    return ((TreeNode<K, V>) first).getTreeNode(hash, key);
                }
                // 方式二：在链表结构里寻找
                do {
                    if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k)))) {
                        return e;
                    }
                } while ((e = e.next) != null);
            }
        }
        return null;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the
     * specified key.
     *
     * @param key The key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified
     * key.
     */
    public boolean containsKey(Object key) {
        return getNode(hash(key), key) != null;
    }

    // eg1: key=0, value="a0"
    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    /**
     * 向HashMap中添加k-v元素
     *
     * @param onlyIfAbsent 如果是true,则不改变已存在的value值
     * @param evict        驱逐，赶出，逐出
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent, boolean evict) {
        Node<K, V>[] tab;
        Node<K, V> p;
        int n, i;

        /** 1：如果是空的table，那么默认初始化一个长度为16的空的Node[]数组 */
        if ((tab = table) == null || (n = tab.length) == 0)
            n = (tab = resize()).length;

        /** 2：如果计算后的下标i，在tab数组中没有数据，那么则直接在下标i处，新增Node节点 */
        if ((p = tab[i = (n - 1) & hash]) == null)
            tab[i] = newNode(hash, key, value, null);

        /** 3：如果计算后的下标i，在tab数组中已存在数据，则执行以下逻辑 */
        else {
            Node<K, V> e;
            K k;

            /** 3-1：如果与已存在的Node是相同的key值 */
            if (p.hash == hash && ((k = p.key) == key || (key != null && key.equals(k))))
                e = p;

            /** 3-2：如果与已存在的Node是相同的key值，并且是树节点 */
            else if (p instanceof TreeNode)
                e = ((TreeNode<K, V>) p).putTreeVal(this, tab, hash, key, value);

            /** 3-3：如果已存在的Node是链表节点，则循环遍历链表，并对比hash和key，如果都不相同，则将新的Node拼装到链表的末尾；如果相同，则对节点的value进行更新 */
            else {
                for (int binCount = 0; ; ++binCount) {  // 【binCount——>链表节点位置】0——>2，7——>9
                    /** case1：如果遍历到了链表的最后一个Node节点，则创建新的节点并拼接到链表尾部，并跳出循环 */
                    if ((e = p.next) == null) {
                        p.next = newNode(hash, key, value, null);
                        // binCount从0开始，也就是链表中第2个node对应binCount=0，如果Node链表大于8个Node，那么试图变为红黑树
                        if (binCount >= TREEIFY_THRESHOLD - 1) treeifyBin(tab, hash);
                        break;
                    }

                    /** case2：如果找到了相同key值的节点，则跳出循环，后续酌情更新节点的value值 */
                    if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
                        break;

                    p = e;
                }
            }

            /** 3-4：如果存在相同的key值 */
            if (e != null) {
                V oldValue = e.value;
                // 如果onlyIfAbsent=false或者oldValue为空，则将新的value值进行更新
                if (!onlyIfAbsent || oldValue == null)
                    e.value = value;
                afterNodeAccess(e); // 空方法
                return oldValue;
            }
        }
        ++modCount;

        /** 4：如果长度超过阈值，则执行扩容操作 */
        if (++size > threshold) resize();

        afterNodeInsertion(evict); // 空方法
        return null;
    }

    /**
     * 执行table扩容操作
     *
     * 常量命名解释：
     *      Tab——>Table 表
     *      Cap——>Capacity 容量
     *      Thr——>Threshold 阈值
     */
    final Node<K, V>[] resize() {
        Node<K, V>[] oldTab = table;                        // 旧的table表
        int oldCap = (oldTab == null) ? 0 : oldTab.length;  // 旧table表的容量
        int oldThr = threshold;                             // 旧table表的阈值
        int newCap = 0;  // 新table表的容量
        int newThr = 0;  // 新table表的阈值

        /**
         * Part 1：根据情况，调整新表的容量newCap和阈值newThr
         */
        /** 1-1：如果老table的容量大于0 **/
        if (oldCap > 0) {
            if (oldCap >= MAXIMUM_CAPACITY) {
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY && oldCap >= DEFAULT_INITIAL_CAPACITY)
                newThr = oldThr << 1; // 新table【阈值】和【容量】都扩容为旧table【阈值】和【容量】的2倍
        }

        /** 1-2：oldCap小于等于0 而 oldThr大于0 */
        else if (oldThr > 0) newCap = oldThr;

        /** 1-3：新的HashMap，第一次请求put方法，创建底层table数组及相关变量 */
        else {
            newCap = DEFAULT_INITIAL_CAPACITY; // 默认值：16
            newThr = (int) (DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY); // 默认为：12
        }

        if (newThr == 0) {
            float ft = (float) newCap * loadFactor;
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float) MAXIMUM_CAPACITY ? (int) ft : Integer.MAX_VALUE);
        }
        threshold = newThr;

        /** 1-4：构建新的table数组 */
        @SuppressWarnings({"rawtypes", "unchecked"})
        Node<K, V>[] newTab = (Node<K, V>[]) new Node[newCap];
        table = newTab;

        /**
         * Part 2：如果老的table里有数据，则进行数据迁移
         */
        if (oldTab != null) {
            /** 2-1：遍历存储于旧table数组中的每条链表 */
            for (int j = 0; j < oldCap; ++j) {
                Node<K, V> e;
                if ((e = oldTab[j]) != null) { // 如果在旧table数组中j的位置存在一条链表，则进行数据迁移操作
                    oldTab[j] = null;

                    /** case1：针对【单节点】进行数据迁移操作*/
                    if (e.next == null)
                        newTab[e.hash & (newCap - 1)] = e;

                    /** case2：针对【红黑树】进行数据迁移操作 */
                    else if (e instanceof TreeNode)
                        ((TreeNode<K, V>) e).split(this, newTab, j, oldCap);

                    /** case3：针对【链表】进行数据迁移操作 */
                    else {
                        Node<K, V> loHead = null;   // 【低位】链表【头】指针
                        Node<K, V> loTail = null;   // 【低位】链表【尾】指针
                        Node<K, V> hiHead = null;   // 【高位】链表【头】指针
                        Node<K, V> hiTail = null;   // 【高位】链表【尾】指针
                        Node<K, V> next;
                        do {
                            next = e.next;
                            /** case3-1：节点e需要被存放在新table的【低位】链表中 */
                            if ((e.hash & oldCap) == 0) { // eg1：oldCap=16=0010000；&计算结果如果为0，说明e.hash的第5位是0，否则是1
                                if (loTail == null) loHead = e; // 设置【头】指针
                                else loTail.next = e;           // 拼装链表
                                loTail = e;                     // 设置【尾】指针
                            }

                            /** case3-2：节点e需要被存放在新table的【高位】链表中 */
                            else {
                                if (hiTail == null) hiHead = e; // 设置【头】指针
                                else hiTail.next = e;           // 拼装链表
                                hiTail = e;                     // 设置【尾】指针
                            }
                        }
                        while ((e = next) != null); // 获取链表的下一个节点

                        /** case3-3：如果存在【低位】链表，则将其赋值到新table中 */
                        if (loTail != null) {
                            loTail.next = null;
                            newTab[j] = loHead;
                        }

                        /** case3-4：如果存在【高位】链表，则将其赋值到新table中 */
                        if (hiTail != null) {
                            hiTail.next = null;
                            newTab[j + oldCap] = hiHead;
                        }
                    }
                }
            }
        }
        return newTab;
    }

    /**
     * 替换bin中给定哈希索引处的所有链接节点，除非表太小，在这种情况下调整大小。
     */
    final void treeifyBin(Node<K, V>[] tab, int hash) {
        int n;
        int index;
        Node<K, V> e;

        /** 1：当表tab的长度小于64时，只扩展数组大小，不转换为红黑树 */
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            resize();

        /** 2：如果新增的node要插入的数组位置已经有链表存在了，则将该链表转换为红黑树 */
        else if ((e = tab[index = (n - 1) & hash]) != null) {
            /** 2-1：遍历链表中每个节点，将Node转化为TreeNode，然后构建新的TreeNode链表 */
            TreeNode<K, V> hd = null; // 指向头节点
            TreeNode<K, V> tl = null; // 指向尾节点
            do {
                TreeNode<K, V> p = replacementTreeNode(e, null); // Node——>TreeNode
                if (tl == null) {
                    hd = p;
                } else {
                    p.prev = tl;
                    tl.next = p;
                }
                tl = p;
            } while ((e = e.next) != null);

            /** 2-2：如果头节点hd不为null，则TreeNode链表进行树型化操作 */
            if ((tab[index] = hd) != null)
                hd.treeify(tab); // 构建红黑树结构
        }
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }

    /**
     * Removes the mapping for the specified key from this map if present.
     *
     * @param key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     * <tt>null</tt> if there was no mapping for <tt>key</tt>.
     * (A <tt>null</tt> return can also indicate that the map
     * previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V remove(Object key) {
        Node<K, V> e;
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
                null : e.value;
    }

    /**
     * Implements Map.remove and related methods.
     *
     * @param hash       hash for key
     * @param key        the key
     * @param value      the value to match if matchValue, else ignored
     * @param matchValue if true only remove if value is equal
     * @param movable    if false do not move other nodes while removing
     * @return the node, or null if none
     */
    final Node<K, V> removeNode(int hash, Object key, Object value,
                                boolean matchValue, boolean movable) {
        Node<K, V>[] tab;
        Node<K, V> p;
        int n, index;
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (p = tab[index = (n - 1) & hash]) != null) {
            Node<K, V> node = null, e;
            K k;
            V v;
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k)))) {
                node = p;
            } else if ((e = p.next) != null) {
                if (p instanceof TreeNode) {
                    node = ((TreeNode<K, V>) p).getTreeNode(hash, key);
                } else {
                    do {
                        if (e.hash == hash &&
                                ((k = e.key) == key ||
                                         (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }
            if (node != null && (!matchValue || (v = node.value) == value ||
                                         (value != null && value.equals(v)))) {
                if (node instanceof TreeNode) {
                    ((TreeNode<K, V>) node).removeTreeNode(this, tab, movable);
                } else if (node == p) {
                    tab[index] = node.next;
                } else {
                    p.next = node.next;
                }
                ++modCount;
                --size;
                afterNodeRemoval(node);
                return node;
            }
        }
        return null;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear() {
        Node<K, V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0) {
            size = 0;
            for (int i = 0; i < tab.length; ++i) {
                tab[i] = null;
            }
        }
    }

    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     * specified value
     */
    public boolean containsValue(Object value) {
        Node<K, V>[] tab;
        V v;
        if ((tab = table) != null && size > 0) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                    if ((v = e.value) == value ||
                            (value != null && value.equals(v))) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation), the results of
     * the iteration are undefined.  The set supports element removal,
     * which removes the corresponding mapping from the map, via the
     * <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt>, and <tt>clear</tt>
     * operations.  It does not support the <tt>add</tt> or <tt>addAll</tt>
     * operations.
     *
     * @return a set view of the keys contained in this map
     */
    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new KeySet();
            keySet = ks;
        }
        return ks;
    }

    final class KeySet extends AbstractSet<K> {
        public final int size() {
            return size;
        }

        public final void clear() {
            HashMap.this.clear();
        }

        public final Iterator<K> iterator() {
            return new KeyIterator();
        }

        public final boolean contains(Object o) {
            return containsKey(o);
        }

        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }

        public final Spliterator<K> spliterator() {
            return new KeySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super K> action) {
            Node<K, V>[] tab;
            if (action == null) {
                throw new NullPointerException();
            }
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                        action.accept(e.key);
                    }
                }
                if (modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own <tt>remove</tt> operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a view of the values contained in this map
     */
    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    final class Values extends AbstractCollection<V> {
        public final int size() {
            return size;
        }

        public final void clear() {
            HashMap.this.clear();
        }

        public final Iterator<V> iterator() {
            return new ValueIterator();
        }

        public final boolean contains(Object o) {
            return containsValue(o);
        }

        public final Spliterator<V> spliterator() {
            return new ValueSpliterator<>(HashMap.this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super V> action) {
            Node<K, V>[] tab;
            if (action == null) {
                throw new NullPointerException();
            }
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                        action.accept(e.value);
                    }
                }
                if (modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation, or through the
     * <tt>setValue</tt> operation on a map entry returned by the
     * iterator) the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and
     * <tt>clear</tt> operations.  It does not support the
     * <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a set view of the mappings contained in this map
     */
    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es;
        return (es = entrySet) == null ? (entrySet = new EntrySet()) : es;
    }

    final class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public final int size() {
            return size;
        }

        public final void clear() {
            HashMap.this.clear();
        }

        public final Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
        }

        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) {
                return false;
            }
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            Object key = e.getKey();
            Node<K, V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }

        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }

        public final Spliterator<Map.Entry<K, V>> spliterator() {
            return new EntrySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super Map.Entry<K, V>> action) {
            Node<K, V>[] tab;
            if (action == null) {
                throw new NullPointerException();
            }
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                        action.accept(e);
                    }
                }
                if (modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }
    }

    // Overrides of JDK8 Map extension methods

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        Node<K, V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }

    @Override
    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }

    @Override
    public boolean remove(Object key, Object value) {
        return removeNode(hash(key), key, value, true, true) != null;
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        Node<K, V> e;
        V v;
        if ((e = getNode(hash(key), key)) != null &&
                ((v = e.value) == oldValue || (v != null && v.equals(oldValue)))) {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }

    @Override
    public V replace(K key, V value) {
        Node<K, V> e;
        if ((e = getNode(hash(key), key)) != null) {
            V oldValue = e.value;
            e.value = value;
            afterNodeAccess(e);
            return oldValue;
        }
        return null;
    }

    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) {
            throw new NullPointerException();
        }
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0) {
            n = (tab = resize()).length;
        }
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode) {
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            } else {
                Node<K, V> e = first;
                K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null) {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null) {
            return null;
        } else if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        } else if (t != null) {
            t.putTreeVal(this, tab, hash, key, v);
        } else {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1) {
                treeifyBin(tab, hash);
            }
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) {
            throw new NullPointerException();
        }
        Node<K, V> e;
        V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
                (oldValue = e.value) != null) {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null) {
                e.value = v;
                afterNodeAccess(e);
                return v;
            } else {
                removeNode(hash, key, null, false, true);
            }
        }
        return null;
    }

    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) {
            throw new NullPointerException();
        }
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0) {
            n = (tab = resize()).length;
        }
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode) {
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            } else {
                Node<K, V> e = first;
                K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            } else {
                removeNode(hash, key, null, false, true);
            }
        } else if (v != null) {
            if (t != null) {
                t.putTreeVal(this, tab, hash, key, v);
            } else {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1) {
                    treeifyBin(tab, hash);
                }
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }

    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null) {
            throw new NullPointerException();
        }
        if (remappingFunction == null) {
            throw new NullPointerException();
        }
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0) {
            n = (tab = resize()).length;
        }
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode) {
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            } else {
                Node<K, V> e = first;
                K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null) {
            V v;
            if (old.value != null) {
                v = remappingFunction.apply(old.value, value);
            } else {
                v = value;
            }
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            } else {
                removeNode(hash, key, null, false, true);
            }
            return v;
        }
        if (value != null) {
            if (t != null) {
                t.putTreeVal(this, tab, hash, key, value);
            } else {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1) {
                    treeifyBin(tab, hash);
                }
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        Node<K, V>[] tab;
        if (action == null) {
            throw new NullPointerException();
        }
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                    action.accept(e.key, e.value);
                }
            }
            if (modCount != mc) {
                throw new ConcurrentModificationException();
            }
        }
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        Node<K, V>[] tab;
        if (function == null) {
            throw new NullPointerException();
        }
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc) {
                throw new ConcurrentModificationException();
            }
        }
    }

    /* ------------------------------------------------------------ */
    // Cloning and serialization

    /**
     * Returns a shallow copy of this <tt>HashMap</tt> instance: the keys and
     * values themselves are not cloned.
     *
     * @return a shallow copy of this map
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object clone() {
        HashMap<K, V> result;
        try {
            result = (HashMap<K, V>) super.clone();
        } catch (CloneNotSupportedException e) {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();
        result.putMapEntries(this, false);
        return result;
    }

    // These methods are also used when serializing HashSets
    final float loadFactor() {
        return loadFactor;
    }

    final int capacity() {
        return (table != null) ? table.length :
                (threshold > 0) ? threshold :
                        DEFAULT_INITIAL_CAPACITY;
    }

    /**
     * Save the state of the <tt>HashMap</tt> instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData The <i>capacity</i> of the HashMap (the length of the
     * bucket array) is emitted (int), followed by the
     * <i>size</i> (an int, the number of key-value
     * mappings), followed by the key (Object) and value (Object)
     * for each key-value mapping.  The key-value mappings are
     * emitted in no particular order.
     */
    private void writeObject(java.io.ObjectOutputStream s)
            throws IOException {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }

    /**
     * Reconstitutes this map from a stream (that is, deserializes it).
     *
     * @param s the stream
     * @throws ClassNotFoundException if the class of a serialized object
     *                                could not be found
     * @throws IOException            if an I/O error occurs
     */
    private void readObject(java.io.ObjectInputStream s)
            throws IOException, ClassNotFoundException {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor)) {
            throw new InvalidObjectException("Illegal load factor: " +
                    loadFactor);
        }
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0) {
            throw new InvalidObjectException("Illegal mappings count: " +
                    mappings);
        } else if (mappings > 0) { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float) mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                               DEFAULT_INITIAL_CAPACITY :
                    (fc >= MAXIMUM_CAPACITY) ?
                            MAXIMUM_CAPACITY :
                            tableSizeFor((int) fc));
            float ft = (float) cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                                 (int) ft : Integer.MAX_VALUE);

            // Check Map.Entry[].class since it's the nearest public type to
            // what we're actually creating.
            SharedSecrets.getJavaOISAccess().checkArray(s, Map.Entry[].class, cap);
            @SuppressWarnings({"rawtypes", "unchecked"})
            Node<K, V>[] tab = (Node<K, V>[]) new Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++) {
                @SuppressWarnings("unchecked")
                K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }

    /* ------------------------------------------------------------ */
    // iterators

    abstract class HashIterator {
        Node<K, V> next;        // next entry to return
        Node<K, V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            Node<K, V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {
                } while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K, V> nextNode() {
            Node<K, V>[] t;
            Node<K, V> e = next;
            if (modCount != expectedModCount) {
                throw new ConcurrentModificationException();
            }
            if (e == null) {
                throw new NoSuchElementException();
            }
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {
                } while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            Node<K, V> p = current;
            if (p == null) {
                throw new IllegalStateException();
            }
            if (modCount != expectedModCount) {
                throw new ConcurrentModificationException();
            }
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class KeyIterator extends HashIterator
            implements Iterator<K> {
        public final K next() {
            return nextNode().key;
        }
    }

    final class ValueIterator extends HashIterator
            implements Iterator<V> {
        public final V next() {
            return nextNode().value;
        }
    }

    final class EntryIterator extends HashIterator
            implements Iterator<Map.Entry<K, V>> {
        public final Map.Entry<K, V> next() {
            return nextNode();
        }
    }

    /* ------------------------------------------------------------ */
    // spliterators

    static class HashMapSpliterator<K, V> {
        final HashMap<K, V> map;
        Node<K, V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMap<K, V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                HashMap<K, V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                Node<K, V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }

    static final class KeySpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<K> {
        KeySpliterator(HashMap<K, V> m, int origin, int fence, int est,
                       int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public KeySpliterator<K, V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action) {
            int i, hi, mc;
            if (action == null) {
                throw new NullPointerException();
            }
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            } else {
                mc = expectedModCount;
            }
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K, V> p = current;
                current = null;
                do {
                    if (p == null) {
                        p = tab[i++];
                    } else {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }

        public boolean tryAdvance(Consumer<? super K> action) {
            int hi;
            if (action == null) {
                throw new NullPointerException();
            }
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null) {
                        current = tab[index++];
                    } else {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount) {
                            throw new ConcurrentModificationException();
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }

    static final class ValueSpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<V> {
        ValueSpliterator(HashMap<K, V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public ValueSpliterator<K, V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action) {
            int i, hi, mc;
            if (action == null) {
                throw new NullPointerException();
            }
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            } else {
                mc = expectedModCount;
            }
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K, V> p = current;
                current = null;
                do {
                    if (p == null) {
                        p = tab[i++];
                    } else {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }

        public boolean tryAdvance(Consumer<? super V> action) {
            int hi;
            if (action == null) {
                throw new NullPointerException();
            }
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null) {
                        current = tab[index++];
                    } else {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount) {
                            throw new ConcurrentModificationException();
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }

    static final class EntrySpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<Map.Entry<K, V>> {
        EntrySpliterator(HashMap<K, V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public EntrySpliterator<K, V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action) {
            int i, hi, mc;
            if (action == null) {
                throw new NullPointerException();
            }
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            } else {
                mc = expectedModCount;
            }
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K, V> p = current;
                current = null;
                do {
                    if (p == null) {
                        p = tab[i++];
                    } else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc) {
                    throw new ConcurrentModificationException();
                }
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K, V>> action) {
            int hi;
            if (action == null) {
                throw new NullPointerException();
            }
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null) {
                        current = tab[index++];
                    } else {
                        Node<K, V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount) {
                            throw new ConcurrentModificationException();
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }

    /* ------------------------------------------------------------ */
    // LinkedHashMap support


    /*
     * The following package-protected methods are designed to be
     * overridden by LinkedHashMap, but not by any other subclass.
     * Nearly all other internal methods are also package-protected
     * but are declared final, so can be used by LinkedHashMap, view
     * classes, and HashSet.
     */

    // Create a regular (non-tree) node
    Node<K, V> newNode(int hash, K key, V value, Node<K, V> next) {
        return new Node<>(hash, key, value, next);
    }

    // 用于从TreeNodes转换为普通的Node节点
    Node<K, V> replacementNode(Node<K, V> p, Node<K, V> next) {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    // Create a tree bin node
    TreeNode<K, V> newTreeNode(int hash, K key, V value, Node<K, V> next) {
        return new TreeNode<>(hash, key, value, next);
    }

    // For treeifyBin
    TreeNode<K, V> replacementTreeNode(Node<K, V> p, Node<K, V> next) {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    /**
     * Reset to initial default state.  Called by clone and readObject.
     */
    void reinitialize() {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }

    // Callbacks to allow LinkedHashMap post-actions
    void afterNodeAccess(Node<K, V> p) { }

    void afterNodeInsertion(boolean evict) { }

    void afterNodeRemoval(Node<K, V> p) { }

    // Called only from writeObject, to ensure compatible ordering.
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        Node<K, V>[] tab;
        if (size > 0 && (tab = table) != null) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }

    static final class TreeNode<K, V> extends LinkedHashMap.Entry<K, V> {
        TreeNode<K, V> parent;  //【树】父节点
        TreeNode<K, V> left;    //【树】左子节点
        TreeNode<K, V> right;   //【树】右子节点
        TreeNode<K, V> prev;    //【链表】前指针
        boolean red;            //【树】默认为黑色

        TreeNode(int hash, K key, V val, Node<K, V> next) {
            super(hash, key, val, next);
        }

        /**
         * 返回红黑树的根节点
         */
        final TreeNode<K, V> root() {
            for (TreeNode<K, V> r = this, p; ; ) {
                /** 如果r没有父节点，则表明r是根节点 */
                if ((p = r.parent) == null)
                    return r;

                /** 否则，沿着父节点往上查找根节点 */
                r = p;
            }
        }

        /**
         * 因为在构造红黑树的过程中，根节点可能会发生变化，所以，通过本方法，来将根节点放到tab数组中。
         * 那么，如果要查找红黑树中的节点，就可以从根节点开始查找了
         */
        static <K, V> void moveRootToFront(Node<K, V>[] tab, TreeNode<K, V> root) {
            int n;
            if (root != null && tab != null && (n = tab.length) > 0) {
                /** 1：计算根节点root在table数组中的存储的下标index位置 */
                int index = (n - 1) & root.hash;

                /** 2：将table数组中下标为index的节点first取出来 */
                TreeNode<K, V> first = (TreeNode<K, V>) tab[index];

                /** 3：如果first节点（tab[index]）不是root节点，则说明链表中的第一个节点需要被更新为root了 */
                if (root != first) {
                    Node<K, V> rn;
                    /** 3-1：将root作为链表中的第1个节点，存储在table数组下标为index的位置中 */
                    tab[index] = root;

                    /** 3-2：将root的前节点与后节点进行连接 */
                    TreeNode<K, V> rp = root.prev;
                    if ((rn = root.next) != null) ((TreeNode<K, V>) rn).prev = rp;
                    if (rp != null) rp.next = rn;

                    /** 3-3：将root节点放置在链表的头部 */
                    if (first != null) first.prev = root;
                    root.next = first;
                    root.prev = null;
                }

                /** 4：对红黑树的规范性进行检查 */
                assert checkInvariants(root);
            }
        }

        /**
         * 查找元素
         * hash值来确定大小
         * key值来确定是否相等
         */
        final TreeNode<K, V> find(int h, Object k, Class<?> kc) {
            // this表示查找操作的起始位置
            TreeNode<K, V> p = this;
            do {
                int ph;
                int dir;
                K pk;
                TreeNode<K, V> pl = p.left;
                TreeNode<K, V> pr = p.right;
                TreeNode<K, V> q;
                if ((ph = p.hash) > h) {
                    p = pl;
                } else if (ph < h) {
                    p = pr;
                } else if ((pk = p.key) == k || (k != null && k.equals(pk))) {
                    return p;
                } else if (pl == null) {
                    p = pr;
                } else if (pr == null) {
                    p = pl;
                } else if ((kc != null || (kc = comparableClassFor(k)) != null) &&
                        (dir = compareComparables(kc, k, pk)) != 0) {
                    p = (dir < 0) ? pl : pr;
                } else if ((q = pr.find(h, k, kc)) != null) {
                    return q;
                } else {
                    p = pl;
                }
            } while (p != null);
            return null;
        }

        /**
         * 从根节点开始，查找元素
         */
        final TreeNode<K, V> getTreeNode(int h, Object k) {
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /**
         * 这是一个打破平局的工具，用于在哈希码相等且不可比较的情况下对插入进行排序。我们不需要一个完全的顺序，只需要一个一致的插入规则来保持在
         * 各个重新平衡中的等价性。打破平局进一步简化了测试。
         *
         *【System.identityHashCode(Object x)】
         *      Object的hashCode方法是根据对象内存地址返回一个hash值，但是很多类都会重写hashCode方法。
         *      JDK在System类中提供一个方法public static native int identityhashCode(Object x)
         *      不管给的参数对象的类是否重载了hashCode（）方法，identityHashCode方法都会返回Object类默认hashCode（）方法会返回的值
         */
        static int tieBreakOrder(Object a, Object b) {
            int d;
            if (a == null || b == null || (d = a.getClass().getName().compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ? -1 : 1); // 如果等于的话，便会返回-1
            return d;
        }

        /**
         * 根据传入的节点列表，塑造红黑树
         */
        final void treeify(Node<K, V>[] tab) {
            TreeNode<K, V> root = null; // 用于存储根节点

            /** 1：循环遍历整个链表，构建红黑树 */
            for (TreeNode<K, V> x = this, next; x != null; x = next) {
                next = (TreeNode<K, V>) x.next;
                x.left = x.right = null; // 清空x节点原有的左右子节点

                /** 1-1：如果是第一个节点，则暂时将其作为根节点 */
                if (root == null) {
                    x.parent = null;    // 设置x节点没有父节点
                    x.red = false;      // 设置x节点是黑色的
                    root = x;           // 将x作为根节点root
                }

                /** 1-2：处理随后的其他节点 */
                else {
                    K k = x.key;        // k：遍历节点x的key值
                    int h = x.hash;     // h：遍历节点x的hash值
                    Class<?> kc = null;

                    /** 开启无限for循环 */
                    for (TreeNode<K, V> p = root; ; ) {
                        int dir;        // dir：【-1】表示左侧节点，【1】表示右侧节点 */
                        int ph;         // ph：parent节点的【hash】值 */
                        K pk = p.key;   // pk：parent节点的【key】值 */

                        /** 1-2-1：如果小于p.hash值，则放到p的左侧，即：dir=-1 */
                        if ((ph = p.hash) > h) dir = -1;

                        /** 1-2-2：如果大于p.hash值，则放到p的右侧，即：dir=1 */
                        else if (ph < h) dir = 1;

                        /** 1-2-3：如果等于p.hash值，则通过Comparable<K>进行对比进行对比，如果还不行，则通过hashCode进行对比 */
                        else if ((kc == null && (kc = comparableClassFor(k)) == null) || // k的类Class不是"class K implements Comparable<K>"的形式
                                (dir = compareComparables(kc, k, pk)) == 0) // 无法通过Comparable<K>进行对比，或者对比结果相等
                            dir = tieBreakOrder(k, pk);

                        /** 1-2-4：试图将x放到p的左子节点或右子节点 */
                        TreeNode<K, V> xp = p;
                        // p默认是指向root节点的，然后通过这段代码，p会向下（子节点）移动
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            x.parent = xp;
                            if (dir <= 0) xp.left = x;
                            else xp.right = x;
                            root = balanceInsertion(root, x); /** 红黑树自平衡操作 */
                            break;
                        }
                    }
                }
            }

            /** 2：将红黑树的根节点移动到链表的头部 */
            moveRootToFront(tab, root);
        }

        /**
         * 将红黑树转退化成单向链表
         */
        final Node<K, V> untreeify(HashMap<K, V> map) {
            Node<K, V> hd = null;   // head头节点
            Node<K, V> tl = null;   // tail尾节点
            for (Node<K, V> q = this; q != null; q = q.next) {  // eg1：q=loHead or q=hiHead
                Node<K, V> p = map.replacementNode(q, null);    // 将TreeNodes节点转换为普通的Node节点
                if (tl == null) hd = p; // 设置【头】指针
                else tl.next = p;       // 拼装链表
                tl = p;                 // 设置【尾】指针
            }
            return hd;
        }

        /**
         * 将数据插入到红黑树中
         */
        final TreeNode<K, V> putTreeVal(HashMap<K, V> map, Node<K, V>[] tab, int h, K k, V v) {
            Class<?> kc = null;
            boolean searched = false;
            /** 获得根节点 */
            TreeNode<K, V> root = (parent != null) ? root() : this;

            /** 1：确定插入节点在红黑树中存放的位置 */
            for (TreeNode<K, V> p = root; ; ) { // 开启无限for循环
                int dir;    // dir：大于0表示右侧节点，否则表示左侧节点
                int ph;     // ph：parent节点的hash值
                K pk;
                /** 2-1：如果小于p.hash值，则放到p的左侧，即：dir=-1 */
                if ((ph = p.hash) > h) dir = -1;

                /** 2-2：如果大于p.hash值，则放到p的右侧，即：dir=1 */
                else if (ph < h) dir = 1;

                /** 2-3：如果等于p.key值，则将该树节点返回 */
                else if ((pk = p.key) == k || (k != null && k.equals(pk))) return p;

                /** 2-4：否则，则通过Comparable<K>进行对比进行对比，如果还不行，则通过hashCode进行对比*/
                else if ((kc == null && (kc = comparableClassFor(k)) == null) || (dir = compareComparables(kc, k, pk)) == 0) {
                    if (!searched) {
                        TreeNode<K, V> q, ch;
                        searched = true;
                        if (((ch = p.left) != null && (q = ch.find(h, k, kc)) != null) ||
                                ((ch = p.right) != null && (q = ch.find(h, k, kc)) != null)) {
                            return q;
                        }
                    }
                    dir = tieBreakOrder(k, pk); // System.identityHashCode
                }

                /** 2：如果待插入的位置为null，则将节点x插入到p的左叶子或右叶子中，并重塑红黑树，保证树结构符合红黑树的规范 */
                TreeNode<K, V> xp = p;
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    /** 2-1：将新增节点维护到红黑树中 */
                    Node<K, V> xpn = xp.next;
                    TreeNode<K, V> x = map.newTreeNode(h, k, v, xpn); // 创建树节点，xp<——>x<——>xpn
                    if (dir <= 0)
                        xp.left = x; // 如果dir小于等于0，则插入到父节点的左侧
                    else
                        xp.right = x; // 如果dir大于等于0，则插入到父节点的右侧

                    /** 2-2：将新增节点维护到双向链表中 */
                    xp.next = x;
                    x.parent = x.prev = xp;
                    if (xpn != null)
                        ((TreeNode<K, V>) xpn).prev = x;

                    /** 2-3：重塑红黑树，并保证保存在tab数组中的节点是root节点 */
                    moveRootToFront(tab, balanceInsertion(root, x));

                    return null;
                }
            }
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         */
        final void removeTreeNode(HashMap<K, V> map, Node<K, V>[] tab, boolean movable) {
            int n;
            if (tab == null || (n = tab.length) == 0) {
                return;
            }
            int index = (n - 1) & hash;
            TreeNode<K, V> first = (TreeNode<K, V>) tab[index], root = first, rl;
            TreeNode<K, V> succ = (TreeNode<K, V>) next, pred = prev;
            if (pred == null) {
                tab[index] = first = succ;
            } else {
                pred.next = succ;
            }
            if (succ != null) {
                succ.prev = pred;
            }
            if (first == null) {
                return;
            }
            if (root.parent != null) {
                root = root.root();
            }
            if (root == null ||
                    (movable && (root.right == null || (rl = root.left) == null || rl.left == null))) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            TreeNode<K, V> p = this;
            TreeNode<K, V> pl = left;
            TreeNode<K, V> pr = right;
            TreeNode<K, V> replacement;
            if (pl != null && pr != null) {
                TreeNode<K, V> s = pr, sl;
                while ((sl = s.left) != null) {// find successor
                    s = sl;
                }
                boolean c = s.red;
                s.red = p.red;
                p.red = c; // swap colors
                TreeNode<K, V> sr = s.right;
                TreeNode<K, V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                } else {
                    TreeNode<K, V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left) {
                            sp.left = p;
                        } else {
                            sp.right = p;
                        }
                    }
                    if ((s.right = pr) != null) {
                        pr.parent = s;
                    }
                }
                p.left = null;
                if ((p.right = sr) != null) {
                    sr.parent = p;
                }
                if ((s.left = pl) != null) {
                    pl.parent = s;
                }
                if ((s.parent = pp) == null) {
                    root = s;
                } else if (p == pp.left) {
                    pp.left = s;
                } else {
                    pp.right = s;
                }
                if (sr != null) {
                    replacement = sr;
                } else {
                    replacement = p;
                }
            } else if (pl != null) {
                replacement = pl;
            } else if (pr != null) {
                replacement = pr;
            } else {
                replacement = p;
            }
            if (replacement != p) {
                TreeNode<K, V> pp = replacement.parent = p.parent;
                if (pp == null) {
                    root = replacement;
                } else if (p == pp.left) {
                    pp.left = replacement;
                } else {
                    pp.right = replacement;
                }
                p.left = p.right = p.parent = null;
            }

            TreeNode<K, V> r = p.red ? root : balanceDeletion(root, replacement);
            if (replacement == p) {  // detach
                TreeNode<K, V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left) {
                        pp.left = null;
                    } else if (p == pp.right) {
                        pp.right = null;
                    }
                }
            }
            if (movable) {
                moveRootToFront(tab, r);
            }
        }

        /**
         * 拆分红黑树
         *
         * 1> 将红黑树拆分成两条TreeNode链表——即：【低位TreeNode链表】和【高位TreeNode链表】
         * 2> 如果【低位TreeNode链表】或【高位TreeNode链表】中的元素小于等于6，则转换为Node类型的单向链表
         * 3> 否则，将【低位TreeNode链表】和【高位TreeNode链表】重塑成两个全新的红黑树
         *
         * @param map   HashMap自身实例
         * @param tab   新的tab数组
         * @param index 下标
         * @param bit   旧tab数组容量
         */
        final void split(HashMap<K, V> map, Node<K, V>[] tab, int index, int bit) {
            TreeNode<K, V> b = this;        // this就是当前树的root节点
            TreeNode<K, V> loHead = null;   // 【低位】链表【头】指针
            TreeNode<K, V> loTail = null;   // 【低位】链表【尾】指针
            TreeNode<K, V> hiHead = null;   // 【高位】链表【头】指针
            TreeNode<K, V> hiTail = null;   // 【高位】链表【尾】指针
            int lc = 0; // 低位元素个数
            int hc = 0; // 高位元素个数

            /** 1：从根节点开始（根节点也是链表的头节点），利用链表特性，对每个节点进行重新寻址，拆分为【低位】链表和【高位】链表 */
            for (TreeNode<K, V> e = b, next; e != null; e = next) {
                next = (TreeNode<K, V>) e.next;
                e.next = null;

                /** 1-1：节点e需要被存放在新table的【低位】链表中，后续会酌情将链表转换为红黑树 */
                if ((e.hash & bit) == 0) {
                    if ((e.prev = loTail) == null) loHead = e;  // 设置【头】指针
                    else loTail.next = e;                       // 拼装链表
                    loTail = e;                                 // 设置【尾】指针
                    ++lc; // 计算【低位】链表中元素的个数
                }
                /** 1-2：节点e需要被存放在新table的【高位】链表中，后续会酌情将链表转换为红黑树 */
                else {
                    if ((e.prev = hiTail) == null) hiHead = e;  // 设置【头】指针
                    else hiTail.next = e;                       // 拼装链表
                    hiTail = e;                                 // 设置【尾】指针
                    ++hc; // 计算【高位】链表中元素的个数
                }
            }

            /** 2：如果低位TreeNode链表存在，酌情执行：红黑树退化为单向链表 or 双向链表重塑红黑树 */
            if (loHead != null) {
                /** 2-1：如果低位链表中的元素小于等于6，执行：红黑树退化为单向链表 */
                if (lc <= UNTREEIFY_THRESHOLD) tab[index] = loHead.untreeify(map);

                /** 2-2：否则执行：双向链表重塑红黑树 */
                else {
                    tab[index] = loHead;
                    // 如果高位首节点不为空，则说明原来的红黑树已经被拆分成两个部分了，如果还是1个部分，那么也就不用重塑红黑树了
                    if (hiHead != null) loHead.treeify(tab);
                }
            }

            /** 3：如果高位TreeNode链表存在，酌情执行：红黑树退化为单向链表 or 双向链表重塑红黑树 */
            if (hiHead != null) {
                /** 3-1：如果低位链表中的元素小于等于6，执行：红黑树退化为单向链表 */
                if (hc <= UNTREEIFY_THRESHOLD) tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead; // 高位链表迁移到新数组中的下标等于【旧数组下标+旧数组长度】
                    // 如果高位首节点不为空，则说明原来的红黑树已经被拆分成两个部分了，如果还是1个部分，那么也就不用重塑红黑树了
                    if (loHead != null) hiHead.treeify(tab);
                }
            }
        }

        /**
         * 左旋操作
         */
        static <K, V> TreeNode<K, V> rotateLeft(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> r;
            TreeNode<K, V> pp;
            TreeNode<K, V> rl;
            if (p != null && (r = p.right) != null) { // p不为null，并且p节点存在右侧子节点
                /** 1：将r的左侧子节点作为p的右侧子节点 */
                if ((rl = p.right = r.left) != null) rl.parent = p;

                /** 2-1：将p的父节点作为r的父节点，如果p没有父节点，即：pp==null */
                if ((pp = r.parent = p.parent) == null) (root = r).red = false; // 将r变为黑色并作为root节点
                /** 2-2：如果p有父节点pp并且p属于pp的左侧子节点 */
                else if (pp.left == p) pp.left = r; // 更改pp的左侧子节点为r
                /** 2-3：如果p有父节点pp并且p属于pp的右侧子节点 */
                else pp.right = r; // 更改pp的右侧子节点为r

                /** 3：p降级为r的左侧子节点 */
                r.left = p;

                /** 4：r作为p的父节点 */
                p.parent = r;
            }
            return root;
        }

        /**
         * 右旋操作
         */
        static <K, V> TreeNode<K, V> rotateRight(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;

                if ((pp = l.parent = p.parent) == null) (root = l).red = false;
                else if (pp.right == p) pp.right = l;
                else pp.left = l;

                l.right = p;
                p.parent = l;
            }
            return root;
        }

        /**
         * 红黑树自平衡
         *
         * @param root 根节点
         * @param x    新插入红黑树中的节点
         */
        static <K, V> TreeNode<K, V> balanceInsertion(TreeNode<K, V> root, TreeNode<K, V> x) {
            x.red = true; // 新增的TreeNode默认设置为红色

            for (TreeNode<K, V> xp, xpp, xppl, xppr; ; ) {
                /** 1：如果x没有父节点，则将自己变为黑色节点，结束循环 */
                if ((xp = x.parent) == null) { //【赋值】xp=x.parent
                    x.red = false;
                    return x;
                }
                /** 2：父节点是黑色 或者 没有祖父节点，结束循环 */
                else if (!xp.red || (xpp = xp.parent) == null) //【赋值】xpp=xp.parent
                    return root;

                /** 3：如果xp是xpp的左侧子节点 */
                if (xp == (xppl = xpp.left)) { // 【赋值】xppl=xpp.left
                    /** 3-1：【变色】操作：如果xpp存在右子节点 并且 该节点是红色*/
                    if ((xppr = xpp.right) != null && xppr.red) { //【赋值】xppr=xpp.right
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp; // 上移x操作，指向其祖父节点
                    }
                    /** 3-2：【旋转+变色】操作：如果xpp不存在右子节点 或者 该节点是黑色的 */
                    else {
                        /** 3-2-1：将树节点左旋为同一侧节点 */
                        if (x == xp.right) {
                            root = rotateLeft(root, x = xp); // 执行左旋操作，重新【赋值】x
                            xpp = (xp = x.parent) == null ? null : xp.parent; // 重新【赋值】xp和xpp
                        }

                        /** 3-2-2：通过右旋平衡红黑树 */
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateRight(root, xpp); // 执行右旋操作
                            }
                        }
                    }
                }
                /** 4：如果xp是xpp的右侧子节点 */
                else {
                    /** 4-1：【变色】操作：如果xpp存在左子节点 并且 该节点是红色 */
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp; // 上移x操作，指向其祖父节点
                    }
                    /** 4-2：【旋转+变色】操作：如果xpp不存在左子节点 或者 该节点是黑色的 */
                    else {
                        /** 4-2-1：将树节点右旋为同一侧节点 */
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp); // 执行右旋操作
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        /** 4-2-2：通过左旋平衡红黑树 */
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp); // 执行左旋操作
                            }
                        }
                    }
                }
            }
        }

        static <K, V> TreeNode<K, V> balanceDeletion(TreeNode<K, V> root,
                                                     TreeNode<K, V> x) {
            for (TreeNode<K, V> xp, xpl, xpr; ; ) {
                if (x == null || x == root) {
                    return root;
                } else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                } else if (x.red) {
                    x.red = false;
                    return root;
                } else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                                (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        } else {
                            if (sr == null || !sr.red) {
                                if (sl != null) {
                                    sl.red = false;
                                }
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                        null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null) {
                                    sr.red = false;
                                }
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                } else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                                (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        } else {
                            if (sl == null || !sl.red) {
                                if (sr != null) {
                                    sr.red = false;
                                }
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                        null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null) {
                                    sl.red = false;
                                }
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * Recursive invariant check
         * 递归不变检查
         */
        static <K, V> boolean checkInvariants(TreeNode<K, V> t) {
            TreeNode<K, V> tp = t.parent, tl = t.left, tr = t.right,
                    tb = t.prev, tn = (TreeNode<K, V>) t.next;
            if (tb != null && tb.next != t) {
                return false;
            }
            if (tn != null && tn.prev != t) {
                return false;
            }
            if (tp != null && t != tp.left && t != tp.right) {
                return false;
            }
            if (tl != null && (tl.parent != t || tl.hash > t.hash)) {
                return false;
            }
            if (tr != null && (tr.parent != t || tr.hash < t.hash)) {
                return false;
            }
            if (t.red && tl != null && tl.red && tr != null && tr.red) {
                return false;
            }
            if (tl != null && !checkInvariants(tl)) {
                return false;
            }
            if (tr != null && !checkInvariants(tr)) {
                return false;
            }
            return true;
        }
    }

}
