/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package java.lang;
import java.lang.ref.*;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

/**
 * This class provides thread-local variables.  These variables differ from
 * their normal counterparts in that each thread that accesses one (via its
 * {@code get} or {@code set} method) has its own, independently initialized
 * copy of the variable.  {@code ThreadLocal} instances are typically private
 * static fields in classes that wish to associate state with a thread (e.g.,
 * a user ID or Transaction ID).
 *
 * <p>For example, the class below generates unique identifiers local to each
 * thread.
 * A thread's id is assigned the first time it invokes {@code ThreadId.get()}
 * and remains unchanged on subsequent calls.
 * <pre>
 * import java.util.concurrent.atomic.AtomicInteger;
 *
 * public class ThreadId {
 *     // Atomic integer containing the next thread ID to be assigned
 *     private static final AtomicInteger nextId = new AtomicInteger(0);
 *
 *     // Thread local variable containing each thread's ID
 *     private static final ThreadLocal&lt;Integer&gt; threadId =
 *         new ThreadLocal&lt;Integer&gt;() {
 *             &#64;Override protected Integer initialValue() {
 *                 return nextId.getAndIncrement();
 *         }
 *     };
 *
 *     // Returns the current thread's unique ID, assigning it if necessary
 *     public static int get() {
 *         return threadId.get();
 *     }
 * }
 * </pre>
 * <p>Each thread holds an implicit reference to its copy of a thread-local
 * variable as long as the thread is alive and the {@code ThreadLocal}
 * instance is accessible; after a thread goes away, all of its copies of
 * thread-local instances are subject to garbage collection (unless other
 * references to these copies exist).
 *
 * @author  Josh Bloch and Doug Lea
 * @since   1.2
 */
public class ThreadLocal<T> {
    /**
     * ThreadLocals rely on per-thread linear-probe hash maps attached
     * to each thread (Thread.threadLocals and
     * inheritableThreadLocals).  The ThreadLocal objects act as keys,
     * searched via threadLocalHashCode.  This is a custom hash code
     * (useful only within ThreadLocalMaps) that eliminates collisions
     * in the common case where consecutively constructed ThreadLocals
     * are used by the same threads, while remaining well-behaved in
     * less common cases.
     */
    private final int threadLocalHashCode = nextHashCode();

    /**
     * The next hash code to be given out. Updated atomically. Starts at
     * zero.
     */
    private static AtomicInteger nextHashCode = new AtomicInteger();

    /**
     * The difference between successively generated hash codes - turns
     * implicit sequential thread-local IDs into near-optimally spread
     * multiplicative hash values for power-of-two-sized tables.
     */
    private static final int HASH_INCREMENT = 0x61c88647;

    /**
     * Returns the next hash code.
     */
    private static int nextHashCode() {
        return nextHashCode.getAndAdd(HASH_INCREMENT);
    }

    /**
     * Returns the current thread's "initial value" for this
     * thread-local variable.  This method will be invoked the first
     * time a thread accesses the variable with the {@link #get}
     * method, unless the thread previously invoked the {@link #set}
     * method, in which case the {@code initialValue} method will not
     * be invoked for the thread.  Normally, this method is invoked at
     * most once per thread, but it may be invoked again in case of
     * subsequent invocations of {@link #remove} followed by {@link #get}.
     *
     * <p>This implementation simply returns {@code null}; if the
     * programmer desires thread-local variables to have an initial
     * value other than {@code null}, {@code ThreadLocal} must be
     * subclassed, and this method overridden.  Typically, an
     * anonymous inner class will be used.
     *
     * @return the initial value for this thread-local
     */
    protected T initialValue() {
        return null;
    }

    /**
     * Creates a thread local variable. The initial value of the variable is
     * determined by invoking the {@code get} method on the {@code Supplier}.
     *
     * @param <S> the type of the thread local's value
     * @param supplier the supplier to be used to determine the initial value
     * @return a new thread local variable
     * @throws NullPointerException if the specified supplier is null
     * @since 1.8
     */
    public static <S> ThreadLocal<S> withInitial(Supplier<? extends S> supplier) {
        return new SuppliedThreadLocal<>(supplier);
    }

    /**
     * Creates a thread local variable.
     * @see #withInitial(java.util.function.Supplier)
     */
    public ThreadLocal() {
    }

    /**
     * Returns the value in the current thread's copy of this
     * thread-local variable.  If the variable has no value for the
     * current thread, it is first initialized to the value returned
     * by an invocation of the {@link #initialValue} method.
     *
     * @return the current thread's value of this thread-local
     */
    public T get() {
        Thread t = Thread.currentThread();
        ThreadLocalMap map = getMap(t);
        if (map != null) {
            ThreadLocalMap.Entry e = map.getEntry(this);
            if (e != null) {
                @SuppressWarnings("unchecked")
                T result = (T)e.value;
                return result;
            }
        }
        return setInitialValue();
    }

    /**
     * Variant of set() to establish initialValue. Used instead
     * of set() in case user has overridden the set() method.
     *
     * @return the initial value
     */
    private T setInitialValue() {
        T value = initialValue();
        Thread t = Thread.currentThread();
        ThreadLocalMap map = getMap(t);
        if (map != null)
            map.set(this, value);
        else
            createMap(t, value);
        return value;
    }

    /**
     * 向ThreadLocal中赋值，如果map为空，则创建ThreadLocalMap
     */
    public void set(T value) {
        /** 1：从当前线程中获取map */
        Thread t = Thread.currentThread();

        ThreadLocalMap map = getMap(t);

        /** 2-1：如果map不为空，则向map中添加value值 */
        if (map != null) map.set(this, value);

        /** 2-2：如果获取不到map，则创建新的ThreadLocalMap实例 */
        else createMap(t, value);
    }

    /**
     * Removes the current thread's value for this thread-local
     * variable.  If this thread-local variable is subsequently
     * {@linkplain #get read} by the current thread, its value will be
     * reinitialized by invoking its {@link #initialValue} method,
     * unless its value is {@linkplain #set set} by the current thread
     * in the interim.  This may result in multiple invocations of the
     * {@code initialValue} method in the current thread.
     *
     * @since 1.5
     */
     public void remove() {
         ThreadLocalMap m = getMap(Thread.currentThread());
         if (m != null)
             m.remove(this);
     }

    /**
     * Get the map associated with a ThreadLocal. Overridden in
     * InheritableThreadLocal.
     *
     * @param  t the current thread
     * @return the map
     */
    ThreadLocalMap getMap(Thread t) {
        return t.threadLocals;
    }

    /**
     * 创建ThreadLocalMap实例对象
     */
    void createMap(Thread t, T firstValue) {
        t.threadLocals = new ThreadLocalMap(this, firstValue);
    }

    /**
     * Factory method to create map of inherited thread locals.
     * Designed to be called only from Thread constructor.
     *
     * @param  parentMap the map associated with parent thread
     * @return a map containing the parent's inheritable bindings
     */
    static ThreadLocalMap createInheritedMap(ThreadLocalMap parentMap) {
        return new ThreadLocalMap(parentMap);
    }

    /**
     * Method childValue is visibly defined in subclass
     * InheritableThreadLocal, but is internally defined here for the
     * sake of providing createInheritedMap factory method without
     * needing to subclass the map class in InheritableThreadLocal.
     * This technique is preferable to the alternative of embedding
     * instanceof tests in methods.
     */
    T childValue(T parentValue) {
        throw new UnsupportedOperationException();
    }

    /**
     * An extension of ThreadLocal that obtains its initial value from
     * the specified {@code Supplier}.
     */
    static final class SuppliedThreadLocal<T> extends ThreadLocal<T> {

        private final Supplier<? extends T> supplier;

        SuppliedThreadLocal(Supplier<? extends T> supplier) {
            this.supplier = Objects.requireNonNull(supplier);
        }

        @Override
        protected T initialValue() {
            return supplier.get();
        }
    }

    /**
     * ThreadLocalMap是一种定制的哈希映射，仅适用于维护线程本地值。 不支持在ThreadLocal类之外有任何操作。 该类是包私有的允许在类Thread中
     * 声明字段。 为了帮助处理非常大且长期存在的使用，哈希表条目使用WeakReferences作为键。 但是，由于不使用引用队列，因此只有在表开始耗尽空
     * 间时才能保证删除陈旧条目。
     *
     * 1> 底层是采用Entry[]数组来保存数据的。
     * 2> 通过ThreadLocal的nextHashCode()方法获得哈希值threadLocalHashCode
     * 3> 然后通过threadLocalHashCode & (INITIAL_CAPACITY - 1)获得对应Entry[]数组的下标，来找到对应下标位置。
     * 4> Entry对象是一个弱引用(WeakReference)对象。
     */
    static class ThreadLocalMap {

        static class Entry extends WeakReference<ThreadLocal<?>> {

            // 存入到ThreadLocal的对象
            Object value;

            Entry(ThreadLocal<?> k, Object v) {
                // 将k放入引用（referent）中。如果调用get()方法返回null，则表明该弱引用已经被gc回收。
                super(k);
                value = v;
            }
        }

        // 初始容量，必须是2的幂。
        private static final int INITIAL_CAPACITY = 16;

        // 数据最终是存储到Entry数组中
        private Entry[] table;

        // 数组table中Entry元素的个数
        private int size = 0;

        // 下一次扩容的阈值，默认为0
        private int threshold;

        /** 定义总长度的2/3长度为阈值的长度，到达后会引发扩容 */
        private void setThreshold(int len) {
            threshold = len * 2 / 3;
        }

        /** 获得入参i（数组index）的后一个index，如果i=队尾index，则它的后一个index就是整个数组的队首index，即：index=0 */
        private static int nextIndex(int i, int len) {
            return ((i + 1 < len) ? i + 1 : 0);
        }

        /** 获得入参i（数组index）的前一个index，如果i=0，则它的前一个index就是整个数组的队尾index，即：index=len-1 */
        private static int prevIndex(int i, int len) {
            return ((i - 1 >= 0) ? i - 1 : len - 1);
        }

        /**
         * 初始化ThreadLocalMap
         * 1> 创建底层数据存储的Entry[]数组table(长度为16)
         * 2> 根据hashCode计算出来所在数组的下标i
         * 3> 执行赋值操作
         * 4> 初始化代表table中元素个数i的值
         * 5> 初始化阈值threshold
         */
        ThreadLocalMap(ThreadLocal<?> firstKey, Object firstValue) {
            table = new Entry[INITIAL_CAPACITY];                            // table数组的默认大小为——INITIAL_CAPACITY=16
            int i = firstKey.threadLocalHashCode & (INITIAL_CAPACITY - 1);  // 确定要插入的数组下标
            table[i] = new Entry(firstKey, firstValue);                     // 创建待插入的Entry对象
            size = 1;                                                       // 设置数组table中Entry元素的个数为1
            setThreshold(INITIAL_CAPACITY);                                 // 设置数组table的阈值，总长度2/3
        }

        /**
         * Construct a new map including all Inheritable ThreadLocals
         * from given parent map. Called only by createInheritedMap.
         *
         * @param parentMap the map associated with parent thread.
         */
        private ThreadLocalMap(ThreadLocalMap parentMap) {
            Entry[] parentTable = parentMap.table;
            int len = parentTable.length;
            setThreshold(len);
            table = new Entry[len];

            for (int j = 0; j < len; j++) {
                Entry e = parentTable[j];
                if (e != null) {
                    @SuppressWarnings("unchecked")
                    ThreadLocal<Object> key = (ThreadLocal<Object>) e.get();
                    if (key != null) {
                        Object value = key.childValue(e.value);
                        Entry c = new Entry(key, value);
                        int h = key.threadLocalHashCode & (len - 1);
                        while (table[h] != null)
                            h = nextIndex(h, len);
                        table[h] = c;
                        size++;
                    }
                }
            }
        }

        /**
         * Get the entry associated with key.  This method
         * itself handles only the fast path: a direct hit of existing
         * key. It otherwise relays to getEntryAfterMiss.  This is
         * designed to maximize performance for direct hits, in part
         * by making this method readily inlinable.
         *
         * @param  key the thread local object
         * @return the entry associated with key, or null if no such
         */
        private Entry getEntry(ThreadLocal<?> key) {
            int i = key.threadLocalHashCode & (table.length - 1);
            Entry e = table[i];
            if (e != null && e.get() == key)
                return e;
            else
                return getEntryAfterMiss(key, i, e);
        }

        /**
         * Version of getEntry method for use when key is not found in
         * its direct hash slot.
         *
         * @param  key the thread local object
         * @param  i the table index for key's hash code
         * @param  e the entry at table[i]
         * @return the entry associated with key, or null if no such
         */
        private Entry getEntryAfterMiss(ThreadLocal<?> key, int i, Entry e) {
            Entry[] tab = table;
            int len = tab.length;

            while (e != null) {
                ThreadLocal<?> k = e.get();
                if (k == key)
                    return e;
                if (k == null)
                    expungeStaleEntry(i);
                else
                    i = nextIndex(i, len);
                e = tab[i];
            }
            return null;
        }

        /**
         * 针对指定的ThreadLocal实例对象，存储相关的value值
         *
         * tab:     table数组
         * len:     table数组的长度
         * i:       待插入Entry的下标
         * sz:      插入完Entry之后，最新的table数组长度
         */
        private void set(ThreadLocal<?> key, Object value) {
            Entry[] tab = table;
            int len = tab.length;
            int i = key.threadLocalHashCode & (len-1); // 计算数组的下标i

            /**
             * 首先，我们要先知晓，Entry对象是【弱引用】对象
             * 注意这里循环的条件是e != null，这个很重要，它采用的就是上面讲的开放地址法。
             * 这里遍历的逻辑是，先通过hash找到数组下标，然后寻找相等的ThreadLocal对象，找不到就往下一个index找。
             * --------------------------------------------------------------------------------------------
             * 有3种情况会跳出循环：
             * 【1】找到了相同key的ThreadLocal对象，然后更新value值；
             * 【2】找到了数组中的一个元素Entry，但是key=null，说明虚引用是可被GC回收的状态；
             * 【3】一直往数组下一个index查找，直到下一个index对应的元素为null；
             */
            for (Entry e = tab[i]; e != null; e = tab[i = nextIndex(i, len)]) {
                /** 如果是相同的threadlocal对象，则将value值更新为入参指定的value值 */
                ThreadLocal<?> k = e.get();
                if (k == key) {
                    e.value = value;
                    return;
                }

                /** 如果返回key=null，则表示弱引用的ThreadLocal对象已经是可被GC回收的状态 */
                if (k == null) {
                    replaceStaleEntry(key, value, i); // Stale=陈旧的
                    return;
                }
            }

            /** 走到这里就说明下标为i的位置上，是没有元素的，所以可以直接将新建的Entry元素插入到i这个位置 */
            tab[i] = new Entry(key, value);
            int sz = ++size;
            if (!cleanSomeSlots(i, sz) && sz >= threshold) {
                /** 对table数组和元素进行整理操作 */
                rehash();
            }
        }

        /**
         * Remove the entry for key.
         */
        private void remove(ThreadLocal<?> key) {
            Entry[] tab = table;
            int len = tab.length;
            int i = key.threadLocalHashCode & (len-1);
            for (Entry e = tab[i];
                 e != null;
                 e = tab[i = nextIndex(i, len)]) {
                if (e.get() == key) {
                    e.clear();
                    expungeStaleEntry(i);
                    return;
                }
            }
        }

        /**
         * 替换待清除的Entry
         *
         * @param key           新的key值
         * @param value         新的value值
         * @param staleSlot     待清除的元素下标
         */
        private void replaceStaleEntry(ThreadLocal<?> key, Object value, int staleSlot) {
            Entry[] tab = table;
            int len = tab.length;
            Entry e;

            /** 在以staleSlot为【中轴】，向左遍历遇到的第一个空位置和向右遍历遇到的第一个空位置【之间】，最左侧的第一个陈旧Entry的下标 */
            int slotToExpunge = staleSlot;

            /**
             * 这里采用的是从当前的staleSlot位置向前面遍历，即：i--；
             * 这样是为了把"陈旧"Entry的空间释放出来，避免由于存在很多"陈旧"Entry导致占用过多空间，从而引发一次rehash操作；
             * 如果所有槽位都被占满了，那么就一直循环下去，直到有空的槽位为止；
             */
            for (int i = prevIndex(staleSlot, len); (e = tab[i]) != null; i = prevIndex(i, len))
                if (e.get() == null) slotToExpunge = i; // 如果key==null，则将该下标index置为【待清除的槽位下标】

            /**
             * 这里采用的是从当前的staleSlot位置向后面遍历，即：i++，刚好跟上面相反。
             * 这两个遍历就是为了以staleSlot为起点，在左边遇到的第一个空的entry到右边遇到的第一空的entry之间查询Stale状态的Entry。
             * 注意：在向右遍历的过程中，如果碰巧找到与入参key相同的Entry时，就开始执行清理操作，然后返回。不再继续遍历下去了。
             */
            for (int i = nextIndex(staleSlot, len); (e = tab[i]) != null; i = nextIndex(i, len)) {
                ThreadLocal<?> k = e.get();

                /** 说明之前已经存在相同的key,所以需要替换旧的值并且和前面那个过期的对象的进行交换位置 */
                if (k == key) {
                    e.value = value;
                    tab[i] = tab[staleSlot];
                    tab[staleSlot] = e;

                    /**
                     * 这里的意思就是，前面的第一个for循环(i--)往前查找的时候，在遇到空位置之前，还没有找到陈旧的Entry，那么也就只有
                     * staleSlot这个位置的Entry是陈旧的了；
                     * 由于前面陈旧的对象已经通过交换位置的方式放到index=i上了，所以需要清理的位置是i，而不是传过来的staleSlot
                     */
                    if (slotToExpunge == staleSlot) slotToExpunge = i;

                    /** 进行清理陈旧数据 */
                    cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
                    return;
                }

                /**
                 * slotToExpunge等于staleSlot，说明上一步的向前遍历循环，当还没有找到其他待清除的"陈旧"Entry的时候，就已经找到了空位置。
                 * 那么，会在向后遍历过程中尝试寻找"陈旧"Entry。
                 */
                if (k == null && slotToExpunge == staleSlot) slotToExpunge = i;
            }

            // 将staleSlot位置的Entry中的value设置为可被gc回收，然后创建一个新的Entry放在staleSlot的位置上
            tab[staleSlot].value = null;
            tab[staleSlot] = new Entry(key, value);

            // 如果有其他已经过期的对象，那么需要清理他
            if (slotToExpunge != staleSlot)
                cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
        }

        /**
         * 清除（expunge）陈旧的（stale）Entry
         * @param staleSlot 待清除的槽位
         */
        private int expungeStaleEntry(int staleSlot) {
            Entry[] tab = table;
            int len = tab.length;

            /** 清除staleSlot槽位对应的对象引用 */
            tab[staleSlot].value = null; // help GC
            tab[staleSlot] = null;
            size--; /** 数组中元素总数减1 */

            Entry e;
            int i;
            for (i = nextIndex(staleSlot, len); (e = tab[i]) != null; i = nextIndex(i, len)) {
                ThreadLocal<?> k = e.get();
                /** 如果key==null，则清除掉对应槽位的元素，并且size减1 */
                if (k == null) {
                    e.value = null;
                    tab[i] = null;
                    size--;
                } else {
                    /**
                     * 这里主要的作用是由于采用了开放地址法，所以删除的元素是多个冲突元素中的一个，需要对后面的元素作处理，可以简单理解
                     * 就是让后面的元素往前面移动。
                     */
                    int h = k.threadLocalHashCode & (len - 1); // 应该坐：h   但是我坐在了：i
                    if (h != i) { // 表示k现在所在的位置i并不是它应该在的位置h上。而是由于开放地址法，放到了别的位置上
                        tab[i] = null;

                        while (tab[h] != null) { // 说明hash是有冲突的，那么往后找空的位置
                            h = nextIndex(h, len);
                        }
                        tab[h] = e;
                    }
                }
            }
            return i;
        }

        /**
         * Heuristically scan some cells looking for stale entries.
         * This is invoked when either a new element is added, or
         * another stale one has been expunged. It performs a
         * logarithmic number of scans, as a balance between no
         * scanning (fast but retains garbage) and a number of scans
         * proportional to number of elements, that would find all
         * garbage but would cause some insertions to take O(n) time.
         * 启发式扫描一些单元格以查找陈旧条目。当添加新元素或删除另一个陈旧元素时调用此方法。 它执行对数扫描，作为不扫描（快速但保留垃圾）
         * 和扫描次数与元素数量成正比之间的平衡，这将找到所有垃圾但会导致某些插入花费 O(n) 时间。
         *
         * @param i a position known NOT to hold a stale entry. The
         * scan starts at the element after i.
         *
         * @param n scan control: {@code log2(n)} cells are scanned,
         * unless a stale entry is found, in which case
         * {@code log2(table.length)-1} additional cells are scanned.
         * When called from insertions, this parameter is the number
         * of elements, but when from replaceStaleEntry, it is the
         * table length. (Note: all this could be changed to be either
         * more or less aggressive by weighting n instead of just
         * using straight log n. But this version is simple, fast, and
         * seems to work well.)
         *
         * @return true if any stale entries have been removed.
         *
         * i:一个已知不会持有过时条目的位置。 扫描从i之后的元素开始。
         * n:扫描长度
         */
        private boolean cleanSomeSlots(int i, int n) {
            boolean removed = false;
            Entry[] tab = table;
            int len = tab.length;
            do {
                i = nextIndex(i, len);
                Entry e = tab[i];
                if (e != null && e.get() == null) { // Stale元素
                    n = len;
                    removed = true;
                    i = expungeStaleEntry(i); // 从位置i开始清除Stale元素，并在这个过程中"整理"元素到趋近正确的位置，直到遍历到null的Slot
                }
            } while ( (n >>>= 1) != 0); /** n>>>=1相当于n=n/2 */
            return removed;
        }

        /**
         * 对table数组和元素进行整理操作
         */
        private void rehash() {
            expungeStaleEntries(); /** 清除表中的所有陈旧条目 */

            // Use lower threshold for doubling to avoid hysteresis（使用较低的加倍阈值以避免滞后）
            if (size >= threshold - threshold / 4) {
                resize(); /** 扩容操作 */
            }
        }

        /**
         * table数组容量翻倍
         */
        private void resize() {
            Entry[] oldTab = table;
            int oldLen = oldTab.length;
            /** 将原数组大小扩容2倍 */
            int newLen = oldLen * 2;
            Entry[] newTab = new Entry[newLen];
            int count = 0;
            for (int j = 0; j < oldLen; ++j) {
                Entry e = oldTab[j];
                if (e != null) {
                    ThreadLocal<?> k = e.get();
                    if (k == null) {
                        e.value = null; // Help the GC
                    } else {
                        /**计算旧的Entry在新的table数组中的位置h */
                        int h = k.threadLocalHashCode & (newLen - 1);
                        /**
                         * 如果位置h已经被别的Entry占据了，那么就向后查找空位，直到找到为止
                         */
                        while (newTab[h] != null) {
                            h = nextIndex(h, newLen);
                        }
                        newTab[h] = e;
                        count++;
                    }
                }
            }
            /** 因为使用了新的数组，所以设置一下新的table数组的阈值 */
            setThreshold(newLen);
            size = count;
            table = newTab;
        }

        /**
         * 清除表中的所有陈旧条目
         */
        private void expungeStaleEntries() {
            Entry[] tab = table;
            int len = tab.length;
            for (int j = 0; j < len; j++) {
                Entry e = tab[j];
                if (e != null && e.get() == null) expungeStaleEntry(j);
            }
        }
    }
}
