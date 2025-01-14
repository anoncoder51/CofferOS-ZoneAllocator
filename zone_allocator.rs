use crate::{
    mm::{Order, Virtual, PAGE_MASK, PAGE_SHIFT},
    percpu::PreemptDisabled,
    service::{
        synchronization::locking::{SpinLockGuardUnchecked, SpinLockUnchecked},
        threading::{
            channel::{Receiver, Sender, ChannelInner},
            Current,
            ThreadPinGuard,
        },
    },
};
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::monitor::ComponentGuard;

use super::OnBoot;

use vstd::cell;
use vstd::cell::*;
use vstd::prelude::*;
use vstd::math::*;

#[cfg(feature = "trace_zone")]
mod tracer {
    use crate::service::synchronization::locking::SpinLockUnchecked;
    use core::cell::UnsafeCell;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Event {
        Ne,
        Alloc(usize, &'static core::panic::Location<'static>),
        Dealloc(usize, &'static core::panic::Location<'static>),
    }

    impl core::fmt::Debug for Event {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::Alloc(addr, loc) => write!(f, "Alloc {:x} {:?}", addr, loc),
                Self::Dealloc(addr, loc) => write!(f, "Dealloc {:x} {:?}", addr, loc),
                Self::Ne => write!(f, "Ne"),
            }
        }
    }

    pub struct Tracer<const MAX_ENTRIES: usize> {
        log: UnsafeCell<[Event; MAX_ENTRIES]>,
        idx: AtomicUsize,
        log_lock: SpinLockUnchecked<()>,
    }

    impl<const MAX_ENTRIES: usize> Tracer<MAX_ENTRIES> {
        pub const fn new() -> Self {
            Self {
                log: UnsafeCell::new([Event::Ne; MAX_ENTRIES]),
                idx: AtomicUsize::new(0),
                log_lock: SpinLockUnchecked::new_const(()),
            }
        }

        pub(crate) fn dump(&self) {
            let _guard = self.log_lock.lock();
            for i in 0..self.idx.load(Ordering::Relaxed) {
                unsafe {
                    println!("{:?} {:?}", i, self.log.get().as_ref().unwrap()[i]);
                }
            }
        }

        #[inline]
        pub(crate) fn trace_alloc(
            &self,
            addr: usize,
            caller: &'static core::panic::Location<'static>,
        ) {
            let idx = self.idx.fetch_add(1, Ordering::SeqCst);
            unsafe {
                self.log.get().as_mut().unwrap()[idx] = Event::Alloc(addr, caller);
            }
        }

        #[inline]
        pub(crate) fn trace_dealloc(
            &self,
            addr: usize,
            caller: &'static core::panic::Location<'static>,
        ) {
            let idx = self.idx.fetch_add(1, Ordering::SeqCst);
            unsafe {
                self.log.get().as_mut().unwrap()[idx] = Event::Dealloc(addr, caller);
            }
        }
    }
}

verus! {

// TODO: Check whether this constant makes sense
pub const MAX_DESCRIPTOR_COUNT: usize = 123123123;
// TODO: Check this (maybe 0xffff_8000_0000_0000?)
pub const MAX_ADDR: usize = 0x1_0000;
pub const MAX_ORDER_SIZE: usize = 8388608; // 1 << 22

pub open spec fn round_up_to_page(x: usize) -> usize {
    ((((x as usize) + (PAGE_MASK as usize)) as usize) & (!PAGE_MASK as usize) as usize)
}

pub open spec fn round_down_to_page(x: usize) -> usize {
    x & !PAGE_MASK
}

#[verifier::external_body]
pub proof fn round_up_down_property(x: usize)
    ensures
        round_down_to_page(x) <= x,
        x <= round_up_to_page(x),
        descr_addr_aligned(round_down_to_page(x) as int),
        descr_addr_aligned(round_up_to_page(x) as int),
{
}

#[verifier::external_body]
pub fn min_spec(x: usize, y: usize) -> (ret: usize)
    ensures
        ret as int == min(x as int, y as int)
{
    x.min(y)
}

#[verifier::external_body]
pub proof fn seq_pop_front<T>(tracked s: &mut Seq<T>) -> (tracked ret: Option<T>)
    ensures
        match ret {
            Some(v) => *s =~= old(s).skip(0) && 0 < old(s).len() && v == old(s)[0],
            None => s == old(s) && s.len() == 0,
        }
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn seq_split_front<T>(tracked s: Seq<T>) -> (tracked ret: (T, Seq<T>))
    requires
        s.len() != 0,
    ensures
        ret.0 == s[0],
        ret.1 =~= s.skip(1),
        ret.1.len() + 1 == s.len(),
{
    unimplemented!()
}

#[inline]
#[verifier::external_body]
pub fn trailing_zeros_spec(x: usize) -> (ret: usize)
    requires
        descr_addr_aligned(x as int),
    ensures
        PAGE_SHIFT <= ret && ret < 64
{
    x.trailing_zeros() as usize
}

#[inline]
#[verifier::external_body]
pub fn checked_add_spec(x: usize, y: usize) -> (ret: Option<usize>)
    ensures
        match ret {
            Some(v) => x + y <= usize::MAX && v == x + y,
            None => (usize::MAX as int) < (x as int) + (y as int),
        }
{
    x.checked_add(y)
}

#[inline]
#[verifier::external_body]
pub fn checked_sub_spec(x: usize, y: usize) -> (ret: Option<usize>)
    ensures
        match ret {
            Some(v) => y <= x && v == x - y,
            None => x < y,
        }
{
    x.checked_sub(y)
}

#[verifier::external_body]
pub proof fn order_size_range(order: Order)
    ensures
        0 <= order.size_spec(),
        order.size_spec() <= MAX_ORDER_SIZE,
{
}

// Predicate that checks whether `addr` is properly aligned
pub open spec fn descr_addr_aligned(addr: int) -> bool;

// Alignedness of the address is preserved after adding/subtracting size of order
#[verifier::external_body]
pub proof fn diff_by_order_size(addr: int, order: Order)
    requires
        descr_addr_aligned(addr),
    ensures
        descr_addr_aligned(addr + order.size_spec()),
        descr_addr_aligned(addr - order.size_spec()),
{
}

#[verifier::external_body]
pub proof fn aligned_min_diff(addr1: int, addr2: int)
    requires
        descr_addr_aligned(addr1),
        descr_addr_aligned(addr2),
        addr1 < addr2,
    ensures
        1 << PAGE_SHIFT <= addr2 - addr1,
{
}

#[repr(transparent)]
#[verifier::external_body]
pub struct SpinLockUncheckedUnit(SpinLockUnchecked<()>);

pub struct LockWithSpec<T> {
    pub lock: SpinLockUncheckedUnit,
    pub data: PCell<T>,
}

#[repr(transparent)]
#[verifier::external_body]
pub struct LockWithSpecGuard<'a>(SpinLockGuardUnchecked<'a, ()>);

impl<T> LockWithSpec<T> {
    pub open spec fn wf(&self) -> bool;

    // Invariant on the value of protected resources.
    // Configurable by user (see the spec of `new` function)
    pub open spec fn inv(&self, val: T) -> bool;

    #[verifier::external_body]
    const fn new(t: T, Ghost(f): Ghost<spec_fn(T) -> bool>) -> (ret: Self)
        ensures
            ret.wf(),
            forall|v| f(v) <==> ret.inv(v)
    {
        let lock = SpinLockUnchecked::new(());
        let (data, _) = PCell::new(t);
        Self { lock: SpinLockUncheckedUnit(lock), data }
    }

    #[verifier::external_body]
    fn acquire(&self) -> (ret: (Tracked<cell::PointsTo<T>>, LockWithSpecGuard))
        requires
            self.wf(),
        ensures
            ret.0@.view().pcell === self.data.id(),
            match ret.0@.view().value {
                Some(v) => self.inv(v),
                None => false,
            }
    {
        let guard = self.lock.0.lock();
        (Tracked::assume_new(), LockWithSpecGuard(guard))
    }

    #[verifier::external_body]
    fn release(&self, points_to: Tracked<cell::PointsTo<T>>)
        requires
            self.wf(),
            points_to@.view().pcell === self.data.id(),
            match points_to@.view().value {
                Some(v) => self.inv(v),
                None => false,
            }
    {
    }
}

impl<'a> LockWithSpecGuard<'a> {
    #[inline]
    #[verifier::external_body]
    fn drop(self) {
        drop(self)
    }
}

#[verifier::external_body]
pub tracked struct PointsToNodes {
    no_copy: NoCopy,
}

impl PointsToNodes {
    pub open spec fn wf(&self, desc: &PageDescriptor) -> bool;
    pub open spec fn wf_broken(&self, desc: &PageDescriptor) -> bool;
    pub open spec fn log_size(&self) -> nat;
    pub open spec fn view(self) -> Option<Node>;

    #[verifier::external_body]
    pub proof fn assume_new() -> (tracked ret: Self)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn perm(tracked &self, desc: &PageDescriptor) -> (tracked ret: &PointsTo<Node>)
        requires
            self.wf(desc),
        ensures
            ret@.pcell == desc.node.id(),
            ret@.value == self@,
    {
        unimplemented!()
    }

    // `take_perm` allows one to take the permission temporarily, by breaking the
    // well-formedness of `PointsToNodes`.
    // After using the `PointsTo<Node>` resource, one can restore the well-formedness
    // of `PointsToNodes` by `restore_perm` rule.
    #[verifier::external_body]
    pub proof fn take_perm(tracked &mut self, desc: &PageDescriptor) -> (tracked ret: PointsTo<Node>)
        requires
            old(self).wf(desc),
        ensures
            self.wf_broken(desc),
            self.log_size() == old(self).log_size(),
            ret@.pcell == desc.node.id(),
            ret@.value == old(self)@,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn restore_perm(tracked &mut self, desc: &PageDescriptor, tracked perm: PointsTo<Node>)
        requires
            old(self).wf_broken(desc),
            perm@.pcell == desc.node.id(),
        ensures
            self.wf(desc),
            self.log_size() == old(self).log_size(),
            self@ == perm@.value,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split(
        tracked self,
        descs: &[PageDescriptor],
        descs_len: nat,
        i: nat,
    ) -> (tracked res: (Self, Self))
        requires
            self.wf(&descs[i as int]),
            descs_len_wf(descs, descs_len),
            self.log_size() != 0,
            i + ((1 as usize) << ((self.log_size() - 1) as usize)) < descs_len,
        ensures
            res.0.log_size() == self.log_size() - 1,
            res.1.log_size() == self.log_size() - 1,
            res.0.wf(&descs[i as int]),
            res.0@ == self@,
            res.1.wf(&descs[i as int + ((1 as usize) << ((self.log_size() - 1) as usize))]),
            res.1@.is_some(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn resize(
        tracked self,
        descs: &[PageDescriptor],
        descs_len: nat,
        i: nat,
        new_log_size: nat,
    ) -> (tracked res: Seq<Self>)
        requires
            self.wf(&descs[i as int]),
            descs_len_wf(descs, descs_len),
            new_log_size <= self.log_size(),
            i + ((1 as usize) << (self.log_size() as usize)) < descs_len,
        ensures
            res.len() == (1 as usize) << ((self.log_size() - new_log_size) as usize),
            forall|j: nat| j < res.len() ==> res[j as int].log_size() == new_log_size,
            forall|j: nat| j < res.len() ==> res[j as int].wf(&descs[i + (((1 as usize) << (new_log_size as usize)) as usize) * j]),
            res[0]@ == self@,
            forall|j: nat| 1 <= j && j < res.len() ==> res[j as int]@.is_some(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn merge(
        tracked self,
        tracked target: Self,
        descs: &[PageDescriptor],
        descs_len: nat,
        i: nat,
    ) -> (tracked res: Self)
        requires
            self.wf(&descs[i as int]),
            descs_len_wf(descs, descs_len),
            i + ((1 as usize) << (self.log_size() as usize)) < descs_len,
            target.wf(&descs[i as int + ((1 as usize) << (self.log_size() as usize))]),
            self.log_size() == target.log_size(),
            target@.is_some(),
        ensures
            res.log_size() == self.log_size() + 1,
            res.wf(&descs[i as int]),
            res@ == self@,
    {
        unimplemented!()
    }
}

// FIXME: Verus panics whenever we apply `.view()` on the slice of `PageDescriptor`.
//        This disallows us to get length of the slice in spec scope.
//        So we introduce an auxiliary variable that denotes the length of the slice
//        and assume several trivial specifications.
pub open spec fn descs_len_wf(descs: &[PageDescriptor], descs_len: nat) -> bool;

#[inline]
#[verifier::external_body]
pub fn descs_len_spec(descs: &[PageDescriptor], Ghost(descs_len): Ghost<nat>) -> (ret: usize)
    requires
        descs_len_wf(descs, descs_len),
    ensures
        ret as nat == descs_len,
{
    descs.len()
}

#[inline]
#[verifier::external_body]
pub fn descs_acc_spec(descs: &[PageDescriptor], Ghost(descs_len): Ghost<nat>, i: usize) -> (ret: &PageDescriptor)
    requires
        descs_len_wf(descs, descs_len),
        (i as nat) < descs_len,
    ensures
        *ret == descs[i as int]
{
    &descs[i]
}

/// Apply `get` function on the corresponding per-cpu cache
#[inline]
#[verifier::external_body]
fn per_cpu_cache_do_get(
    allocator: &ZoneAllocator,
    order: Order,
    p: impl PreemptDisabled,
) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
    requires
        match order {
            Order::Order0 | Order::Order1 | Order::Order2 | Order::Order3 => true,
            _ => false,
        },
        allocator.wf(),
    ensures
        match ret {
            Some(v) => {
                &&& v.0.wf()
                &&& v.1@.wf(v.0)
                &&& v.1@.log_size() as int == order.into_int()
                &&& v.1@@.is_some()
                &&& exists|i: nat| allocator.descs.descs[i as int] == *v.0 && i + ((1 as usize) << (v.1@.log_size() as usize)) < allocator.descs.descs_len@
            }
            None => true,
        }
{
    match order {
        Order::Order0 => ORDER0_CACHE.get(p).get(allocator),
        Order::Order1 => ORDER1_CACHE.get(p).get(allocator),
        Order::Order2 => ORDER2_CACHE.get(p).get(allocator),
        Order::Order3 => ORDER3_CACHE.get(p).get(allocator),
        _ => None,
    }
}

/// Apply `put` function on the corresponding per-cpu cache
#[inline]
#[verifier::external_body]
fn per_cpu_cache_do_put(
    allocator: &ZoneAllocator,
    page: &'static PageDescriptor,
    Tracked(pointsto): Tracked<PointsToNodes>,
    order: Order,
    p: impl PreemptDisabled,
) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
    requires
        match order {
            Order::Order0 | Order::Order1 | Order::Order2 | Order::Order3 => true,
            _ => false,
        },
        allocator.wf(),
        page.wf(),
        pointsto.wf(page),
        pointsto@.is_some(),
        pointsto.log_size() as int == order.into_int(),
        exists|i: nat| allocator.descs.descs[i as int] == *page && i + ((1 as usize) << (pointsto.log_size() as usize)) < allocator.descs.descs_len@,
    ensures
        match ret {
            Some(v) => {
                &&& v.0 == page
                &&& v.1@ === pointsto
            }
            None => true,
        }
{
    match order {
        Order::Order0 => ORDER0_CACHE.get(p).put(allocator, page, Tracked(pointsto)),
        Order::Order1 => ORDER1_CACHE.get(p).put(allocator, page, Tracked(pointsto)),
        Order::Order2 => ORDER2_CACHE.get(p).put(allocator, page, Tracked(pointsto)),
        Order::Order3 => ORDER3_CACHE.get(p).put(allocator, page, Tracked(pointsto)),
        _ => None,
    }
}

#[inline]
#[verifier::external_body]
fn preemptdisabled_drop(p: impl PreemptDisabled) {
    drop(p);
}

#[inline]
#[verifier::external_body]
fn current_get_pin() -> ThreadPinGuard {
    Current::get().pin()
}

#[inline]
#[verifier::external_body]
fn virtual_new_wrapper(addr: usize) -> Virtual {
    Virtual::new(addr).unwrap()
}

/// Tag of the memory descriptor union.
#[repr(u64)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tag {
    /// A page is head page owned by Zone.
    ZoneOwned,
    /// A page is head page not owned by Zone.
    InUsed,
    /// A page is trailing page.
    TrailingPage,
}

/// Private data of ZoneOwned page.
///
/// Owned by on zone allocator or slab allocator.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Node {
    /// Is this object owned by zone allocator?
    /// Next node pointer of link list that used on Zone allocator.
    pub next: Option<&'static PageDescriptor>,
    /// Prev node pointer of link list that used on Zone allocator.
    pub prev: Option<&'static PageDescriptor>,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Head {
    // ZoneAloocator modifiable
    pub order: Order,
    #[cfg(not(feature = "single_coffer"))]
    pub owner: crate::monitor::RunId,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Compound {
    // ZoneAloocator modifiable
    pub(crate) head: &'static PageDescriptor,
}

pub union ZoneInfo {
    pub head: Head,
    pub compound: Compound,
}

#[repr(C)]
pub struct Common {
    // ZoneAloocator modifiable
    pub tag: Tag,
    // See ZoneInfo
    pub info: ZoneInfo,
    // A cold value
    pub addr: Virtual,
}

impl Common {
    pub open spec fn wf(&self) -> bool {
        // 1. `self.info` is `head` if self.tag == Tag::ZoneOwned
        // 2. `self.info` is `compound` if self.tag == Tag::TrailingPage
        match self.tag {
            Tag::ZoneOwned => is_variant(self.info, "head"),
            Tag::InUsed => true,
            Tag::TrailingPage => is_variant(self.info, "compound"),
        }
    }
}

/// Page descriptor itself.
#[assert_size(64)]
#[repr(C, align(64))]
pub struct PageDescriptor {
    // This lock serializes zone allocator.
    // Lock protects `PointsTo` resources (in verus) that controls access to `PCell`.
    pub lock: LockWithSpec<Tracked<PointsTo<Common>>>,
    pub common: PCell<Common>,
    pub node: PCell<Node>,
    pub ref_cnt: AtomicUsize,
}

} // verus!

unsafe impl Send for PageDescriptor {}
// Safety: The data is protected with lock.
unsafe impl Sync for PageDescriptor {}

verus! {

impl PageDescriptor {
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& forall|v| self.lock.inv(v) <==> self.lock_res_inv(v)
    }

    pub open spec fn lock_res_inv(&self, v: Tracked<PointsTo<Common>>) -> bool {
        &&& v@@.pcell === self.common.id()
        &&& match v@@.value {
            Some(c) => c.wf(),
            None => false,
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> (guard: PageDescriptorGuard)
        requires
            self.wf(),
        ensures
            self === guard.original,
            guard.wf()
    {
        let (pts, _guard) = self.lock.acquire();

        assert(match pts@@.value {
            Some(v) => self.lock_res_inv(v),
            None => false,
        });

        PageDescriptorGuard {
            original: self,
            lock_acc: pts,
            _guard
        }
    }
}

/// Page descriptor object with guard.
/// Note that verus does not support Deref and DerefMut,
/// hence we include reference to the original PageDescriptor object
/// following verus style.
pub struct PageDescriptorGuard<'a> {
    pub original: &'a PageDescriptor,
    pub lock_acc: Tracked<PointsTo<Tracked<PointsTo<Common>>>>,
    pub _guard: LockWithSpecGuard<'a>,
}

impl<'a> PageDescriptorGuard<'a> {
    // Minimal well-formedness condition to run operations with the guard.
    pub open spec fn wf_weak(&self) -> bool {
        &&& self.original.wf()
        &&& self.original.lock.data.id() === self.lock_acc@@.pcell
        &&& match self.lock_acc@@.value {
                Some(v) => {
                    &&& v@@.pcell === self.original.common.id()
                    &&& v@@.value.is_some()
                }
                None => false,
            }
    }

    // Full well-formedness condition.
    // This may not hold during modification of PageDescriptor's fields.
    pub open spec fn wf(&self) -> bool {
        &&& self.wf_weak()
        &&& match self.lock_acc@@.value {
                Some(v) => self.original.lock_res_inv(v),
                None => false,
            }
    }

    /// Get tag of this descriptor.
    pub fn tag(&self) -> (ret: Tag)
        requires
            self.wf_weak(),
        ensures
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => ret == c.tag,
                    None => false,
                },
                None => false,
            }
    {
        self.borrow_common().tag
    }

    pub fn set_tag(&mut self, new_tag: Tag)
        requires
            old(self).wf_weak()
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                // Tag value is changed.
                                &&& c.tag == new_tag
                                // Other fields are remain unchanged.
                                &&& c.info == oc.info
                                &&& c.addr == oc.addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        c.tag = new_tag;

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    pub fn borrow_common(&self) -> (ret: &Common)
        requires
            self.wf_weak(),
        ensures
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => c === *ret,
                    None => false,
                },
                None => false,
            }
    {
        let acc = self.original.lock.data.borrow(Tracked(self.lock_acc.borrow()));
        self.original.common.borrow(Tracked(acc.borrow()))
    }

    pub fn set_common_info_head(&mut self, head: Head)
        requires
            old(self).wf_weak(),
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                &&& c.tag == oc.tag
                                &&& c.info == ZoneInfo { head }
                                &&& c.addr == oc.addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        c.info = ZoneInfo { head };

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    pub fn set_common_info_head_order(&mut self, order: Order)
        requires
            old(self).wf_weak(),
            match old(self).lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => is_variant(c.info, "head"),
                    None => false,
                }
                None => false,
            }
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                &&& c.tag == oc.tag
                                &&& c.info == ZoneInfo {
                                        head: Head {
                                            order,
                                            #[cfg(not(feature = "single_coffer"))]
                                            owner: get_union_field::<ZoneInfo, Head>(oc.info, "head").owner,
                                        }
                                    }
                                &&& c.addr == oc.addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        unsafe {
            c.info = ZoneInfo {
                head: Head {
                    order,
                    #[cfg(not(feature = "single_coffer"))]
                    owner: c.info.head.owner,
                }
            };
        }

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    #[cfg(not(feature = "single_coffer"))]
    pub fn set_common_info_head_owner(&mut self, owner: crate::monitor::RunId)
        requires
            old(self).wf_weak(),
            match old(self).lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => is_variant(c.info, "head"),
                    None => false,
                }
                None => false,
            }
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                &&& c.tag == oc.tag
                                &&& c.info == ZoneInfo {
                                        head: Head {
                                            order: get_union_field::<ZoneInfo, Head>(oc.info, "head").order,
                                            owner,
                                        }
                                    }
                                &&& c.addr == oc.addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        let order = unsafe { c.info.head.order };
        c.info = ZoneInfo { head: Head { order, owner } };

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    pub fn set_common_info_compound(&mut self, compound: Compound)
        requires
            old(self).wf_weak(),
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                &&& c.tag == oc.tag
                                &&& c.info == ZoneInfo { compound }
                                &&& c.addr == oc.addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        c.info = ZoneInfo { compound };

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    pub fn set_common_addr(&mut self, addr: Virtual)
        requires
            old(self).wf_weak(),
        ensures
            self.wf_weak(),
            self.original == old(self).original,
            match self.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => match old(self).lock_acc@@.value {
                        Some(ov) => match ov@@.value {
                            Some(oc) => {
                                &&& c.tag == oc.tag
                                &&& c.info == oc.info
                                &&& c.addr == addr
                            }
                            None => false,
                        }
                        None => false,
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut c_acc = self.original.lock.data.take(Tracked(&mut self.lock_acc.borrow_mut()));
        let mut c = self.original.common.take(Tracked(&mut c_acc.borrow_mut()));

        c.addr = addr;

        self.original.common.put(Tracked(&mut c_acc.borrow_mut()), c);
        self.original.lock.data.put(Tracked(&mut self.lock_acc.borrow_mut()), c_acc);
    }

    pub fn borrow_node(&self, acc: Tracked<&'a PointsTo<Node>>) -> (ret: &'a Node)
        requires
            self.original.node.id() == acc@@.pcell,
            acc@@.value.is_some(),
        ensures
            match acc@@.value {
                Some(n) => *ret == n,
                None => false,
            }
    {
        self.original.node.borrow(acc)
    }

    pub fn set_node(&self, Tracked(acc): Tracked<&mut PointsTo<Node>>, new_node: Node)
        requires
            self.original.node.id() === old(acc)@.pcell,
            old(acc)@.value.is_some(),
        ensures
            acc@.pcell === old(acc)@.pcell,
            match acc@.value {
                Some(n) => n == new_node,
                None => false,
            }
    {
        let _ = self.original.node.replace(Tracked(acc), new_node);
    }

    pub fn set_node_next(&self, Tracked(acc): Tracked<&mut PointsTo<Node>>, next: Option<&'static PageDescriptor>)
        requires
            self.original.node.id() === old(acc)@.pcell,
            old(acc)@.value.is_some(),
        ensures
            acc@.pcell === old(acc)@.pcell,
            match acc@.value {
                Some(n) => match old(acc)@.value {
                    Some(on) => {
                        &&& n.prev == on.prev
                        &&& n.next == next
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut node = self.original.node.take(Tracked(acc));
        node.next = next;
        self.original.node.put(Tracked(acc), node);
    }

    pub fn set_node_prev(&self, Tracked(acc): Tracked<&mut PointsTo<Node>>, prev: Option<&'static PageDescriptor>)
        requires
            self.original.node.id() === old(acc)@.pcell,
            old(acc)@.value.is_some(),
        ensures
            acc@.pcell === old(acc)@.pcell,
            match acc@.value {
                Some(n) => match old(acc)@.value {
                    Some(on) => {
                        &&& n.prev == prev
                        &&& n.next == on.next
                    }
                    None => false,
                }
                None => false,
            }
    {
        let mut node = self.original.node.take(Tracked(acc));
        node.prev = prev;
        self.original.node.put(Tracked(acc), node);
    }

    #[verifier::external_body]
    fn zeroing(&self, Tracked(pts): Tracked<&mut PointsToNodes>)
        requires
            self.wf_weak(),
            old(pts).wf(&self.original),
        ensures
            pts == old(pts),
    {
        unsafe {
            let common = self.borrow_common();
            core::slice::from_raw_parts_mut(
                common.addr.into_usize() as *mut u64,
                common.info.head.order.size() / 8,
            )
            .fill(0);
        }
    }

    // Verus does not support `drop`
    // so we just assume a specification for dropping the guard.
    #[verifier::external_body]
    fn drop(self)
        requires
            self.wf()
    {
        self.original.lock.release(self.lock_acc);
        drop(self._guard);
    }
}

pub struct PageDescriptors {
    pub base: usize,
    pub descs: &'static [PageDescriptor],
    pub descs_len: Ghost<nat>,
    #[cfg(feature = "ondemand_mm")]
    pub tail: AtomicUsize,
}

#[derive(Clone, Copy)]
pub struct PageDescriptorIndex<'a> {
    pub index: usize,
    pub descs: &'a PageDescriptors,
}

impl PageDescriptors {
    pub open spec fn wf(&self) -> bool {
        &&& forall|i: nat| 0 <= i && i < self.descs_len@ ==> self.descs[i as int].wf()
        &&& descs_len_wf(self.descs, self.descs_len@)
        &&& self.descs_len@ < MAX_DESCRIPTOR_COUNT
        &&& self.is_unique()
    }

    pub open spec fn is_unique(&self) -> bool {
        forall|i: nat, j: nat| i < self.descs_len@ && j < self.descs_len@ && self.descs[i as int] == self.descs[j as int] ==> i == j
    }

    pub proof fn index_unique(&self, i: nat, j: nat)
        requires
            self.wf(),
            i < self.descs_len@,
            j < self.descs_len@,
            self.descs[i as int] == self.descs[j as int],
        ensures
            i == j
    {
    }

    #[inline]
    #[verifier::external_body]
    pub fn try_from_index(&self, index: usize) -> (ret: Option<PageDescriptorIndex>)
        requires
            self.wf(),
        ensures
            match ret {
                Some(idx) => {
                    &&& idx.wf()
                    &&& idx.descs == self
                    &&& idx.index == index
                }
                None => self.descs_len@ <= (index as nat),
            }
    {
        if index < self.descs.len() {
            Some(PageDescriptorIndex { descs: self, index })
        } else {
            None
        }
    }

    #[verifier::external_body]
    pub fn indexed_ref(&self, v: &PageDescriptor, Ghost(i): Ghost<nat>) -> (ret: Option<PageDescriptorIndex>)
        requires
            self.wf(),
            0 <= i,
            i < self.descs_len@,
            self.descs[i as int] == v,
        ensures
            match ret {
                Some(idx) => {
                    &&& idx.wf()
                    &&& idx.descs == self
                    &&& idx.index == i
                }
                None => false,
            }
    {
        self.try_from_index(
            (v as *const _ as usize - self.descs.as_ptr() as usize)
                / core::mem::size_of::<PageDescriptor>(),
        )
    }

    #[verifier::external_body]
    pub fn try_from_addr(&self, addr: usize) -> (ret: Option<PageDescriptorIndex>)
        requires
            self.wf(),
            descr_addr_aligned(addr as int),
        ensures
            match ret {
                Some(idx) => {
                    &&& idx.wf()
                    &&& idx.descs == self
                    &&& idx.is_addr(addr as int)
                }
                None => true,
            }
    {
        self.try_from_index((addr - self.base) >> PAGE_SHIFT)
    }
}

impl<'a> PageDescriptorIndex<'a> {
    pub open spec fn wf(&self) -> bool {
        &&& self.descs.wf()
        &&& (self.index as nat) < self.descs.descs_len@
    }

    pub open spec fn is_addr(&self, addr: int) -> bool;

    #[verifier::external_body]
    pub proof fn addr_diff_by_order(&self, next: &Self, addr: int, order: Order)
        requires
            self.wf(),
            next.wf(),
            self.is_addr(addr),
            next.is_addr(addr + order.size_spec()),
        ensures
            next.index == self.index + ((1 as usize) << (order.into_int() as usize)),
    {
    }

    // Note: Verus fails to notice `Clone` and `Copy` traits for `PageDescriptorIndex`.
    //       Naive implementation triggers an error: "use of moved value".
    //       Hence, we manually duplicate the variable.
    #[inline]
    fn copy(&self) -> (ret: Self)
        ensures
            ret == *self
    {
        PageDescriptorIndex { index: self.index, descs: self.descs }
    }

    #[inline]
    fn get(&self) -> (ret: PageDescriptorGuard)
        requires
            self.wf(),
        ensures
            ret.wf(),
            ret.original == &self.descs.descs[self.index as int],
    {
        unsafe { descs_acc_spec(self.descs.descs, self.descs.descs_len, self.index).get() }
    }

    #[inline]
    #[verifier::external_body]
    // FIXME: Lifetime checking bug
    // "error: lifetime may not live long enough"
    // "note: This error was found in Verus pass: ownership checking of tracked code"
    pub(crate) fn inner(self) -> (ret: &'static PageDescriptor)
        requires
            self.wf(),
        ensures
            ret == &self.descs.descs[self.index as int],
    {
        &self.descs.descs[self.index]
    }

    /// Get frame number of this descriptor.
    #[inline]
    pub fn frame_index(&self) -> (ret: usize)
        ensures
            ret == self.index
    {
        self.index
    }

    #[inline]
    #[verifier::external_body]
    pub fn addr(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            self.is_addr(ret as int),
            descr_addr_aligned(ret as int),
            ret < MAX_ADDR,
    {
        self.descs.base + (self.index << PAGE_SHIFT)
    }
}

pub struct FreeArea {
    pub head: Option<&'static PageDescriptor>,

    // Logical resource that tracks the structure of doubly linked list
    pub ghost_state: Tracked<GhostState>,
}

pub tracked struct GhostState {
    // List of page descriptors consisting of the doubly linked list
    pub ghost ptrs: Seq<&'static PageDescriptor>,
    // Index `i` → PointsTo resource of `i`th node
    pub tracked points_to_map: Map<nat, PointsToNodes>,
    // Each page in the `FreeArea` has equal order
    pub ghost order: Order,
}

impl GhostState {
    pub proof fn update_ptrs(tracked &mut self, new_ptrs: Seq<&'static PageDescriptor>)
        ensures
            self.ptrs === new_ptrs,
            self.points_to_map === old(self).points_to_map,
            self.order === old(self).order,
    {
        self.ptrs = new_ptrs;
    }
}

impl FreeArea {
    pub open spec fn is_prev_wf(&self, i: nat, node: Node) -> bool {
        match node.prev {
            Some(prev) => {
                &&& i != 0
                &&& self.ghost_state@.ptrs[i as int - 1] == &prev
            }
            None => i == 0,
        }
    }

    pub open spec fn is_next_wf(&self, i: nat, node: Node) -> bool {
        match node.next {
            Some(next) => {
                &&& i + 1 < self.ghost_state@.ptrs.len()
                &&& self.ghost_state@.ptrs[i as int + 1] == &next
            }
            None => i + 1 == self.ghost_state@.ptrs.len()
        }
    }

    pub open spec fn is_node_wf(&self, descs: &[PageDescriptor], descs_len: nat, i: nat) -> bool {
        &&& self.ghost_state@.ptrs[i as int].wf()
        &&& self.ghost_state@.points_to_map.dom().contains(i)
        &&& self.ghost_state@.points_to_map[i].wf(self.ghost_state@.ptrs[i as int])
        &&& self.ghost_state@.points_to_map[i].log_size() as int == self.ghost_state@.order.into_int()
        &&& exists|i_descs: nat|
                #[trigger]
                descs[i_descs as int] == self.ghost_state@.ptrs[i as int] &&
                i_descs + ((1 as usize) << (self.ghost_state@.points_to_map[i].log_size() as usize)) < descs_len
        &&& match self.ghost_state@.points_to_map[i]@ {
                Some(n) => self.is_prev_wf(i, n) && self.is_next_wf(i, n),
                None => false,
            }
    }

    // Wellformness
    // for node in self:
    //  node.node().next.prev == node.
    // all elements in fa has same tag.
    pub open spec fn wf(&self, descs: &[PageDescriptor], descs_len: nat) -> bool {
        // Well-formedness of each node in the doubly linked list
        &&& forall|i: nat| 0 <= i && i < self.ghost_state@.ptrs.len() ==> self.is_node_wf(descs, descs_len, i)
        // Doubly linked list should start from the head node
        &&& match self.head {
                Some(desc) => self.ghost_state@.ptrs.len() != 0 && &desc == self.ghost_state@.ptrs[0],
                None => self.ghost_state@.ptrs.len() == 0,
            }
    }

    /// post-condition: self.wf(). head = None.
    pub const fn empty(Ghost(order): Ghost<Order>, Tracked(descs): Tracked<&[PageDescriptor]>, Ghost(descs_len): Ghost<nat>) -> (ret: Self)
        ensures
            ret.wf(descs, descs_len),
            ret.head.is_none(),
            ret.ghost_state@.order == order,
    {
        FreeArea {
            head: None,
            ghost_state: Tracked(GhostState {
                ptrs: Seq::empty(),
                points_to_map: Map::tracked_empty(),
                order,
            }),
        }
    }

    // pre-condition: guard is in the fa. self.wf()
    // post-condition: guard is not in the fa. self.wf()
    fn remove(&mut self, Tracked(descs): Tracked<&[PageDescriptor]>, Ghost(descs_len): Ghost<nat>, mut guard: PageDescriptorGuard) -> (ret: Tracked<PointsToNodes>)
        requires
            old(self).wf(descs, descs_len),
            guard.wf(),
            exists|i: nat| 0 <= i && i < old(self).ghost_state@.ptrs.len() && old(self).ghost_state@.ptrs[i as int] == &guard.original,
        ensures
            self.wf(descs, descs_len),
            self.ghost_state@.order == old(self).ghost_state@.order,
            self.ghost_state@.ptrs.len() + 1 == old(self).ghost_state@.ptrs.len(),
            ret@.wf(&guard.original),
            ret@.log_size() as int == self.ghost_state@.order.into_int(),
            ret@@.is_some(),
            exists|i: nat| descs[i as int] == guard.original && i + ((1 as usize) << (ret@.log_size() as usize)) < descs_len
    {
        let ghost i_witness = choose|i: nat| 0 <= i && i < self.ghost_state@.ptrs.len() && self.ghost_state@.ptrs[i as int] == &guard.original;
        assert(self.is_node_wf(descs, descs_len, i_witness));
        assert(i_witness != 0 ==> self.is_node_wf(descs, descs_len, (i_witness - 1) as nat));
        assert(i_witness + 1 < self.ghost_state@.ptrs.len() ==> self.is_node_wf(descs, descs_len, i_witness + 1));
        assert(self.ghost_state@.points_to_map.dom().contains(i_witness));
        let tracked mut pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(i_witness);
        let node = guard.borrow_node(Tracked(pointsto.perm(self.ghost_state@.ptrs[i_witness as int])));

        match node.prev {
            Some(prev) => {
                assert(self.ghost_state@.ptrs[i_witness as int - 1] == prev);
                let mut pnode = prev.get();
                let tracked mut pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove((i_witness - 1) as nat);
                let tracked mut perm = pointsto.take_perm(self.ghost_state@.ptrs[i_witness - 1]);
                pnode.set_node_next(Tracked(&mut perm), node.next);
                proof {
                    pointsto.restore_perm(self.ghost_state@.ptrs[i_witness - 1], perm);
                    self.ghost_state.borrow_mut().points_to_map.tracked_insert((i_witness - 1) as nat, pointsto);
                }
            }
            None => self.head = node.next,
        }

        if let Some(next) = node.next {
            let mut nnode = next.get();
            let tracked mut pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(i_witness + 1);
            let tracked mut perm = pointsto.take_perm(self.ghost_state@.ptrs[i_witness as int + 1]);
            nnode.set_node_prev(Tracked(&mut perm), node.prev);
            proof {
                pointsto.restore_perm(self.ghost_state@.ptrs[i_witness as int + 1], perm);
                self.ghost_state.borrow_mut().points_to_map.tracked_insert(i_witness + 1, pointsto);
            }
        }
        guard.set_tag(Tag::InUsed);

        // Release the lock acquired by the guard and drop the guard
        assert(match guard.lock_acc@@.value {
            Some(v) => guard.original.lock_res_inv(v),
            None => false,
        });
        guard.drop();

        proof {
            // 1. Remove `i_witness`th element from the `ptrs` sequence
            self.ghost_state.borrow_mut().update_ptrs(self.ghost_state@.ptrs.remove(i_witness as int));
            assert(self.ghost_state@.ptrs.len() == old(self).ghost_state@.ptrs.len() - 1);

            // 2. Adjust the indices of each element in `points_to_map`
            //    so that domain of the map becomes a contiguous range.
            let ghost key_map = Map::<nat, nat>::new(
                |j: nat| 0 <= j && j < self.ghost_state@.ptrs.len(),
                |j: nat| if j < i_witness { j } else { j + 1 }
            );
            assert forall |j: nat| key_map.dom().contains(j) implies self.ghost_state@.points_to_map.dom().contains(key_map.index(j)) by {
                assert(old(self).is_node_wf(descs, descs_len, j));
                assert(old(self).is_node_wf(descs, descs_len, j + 1));
                assert(j < i_witness ==> self.ghost_state@.points_to_map.dom().contains(j));
                assert(i_witness <= j ==> self.ghost_state@.points_to_map.dom().contains(j + 1));
            }
            self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(key_map);

            // 3. Re-establish the well-formedness condition of FreeArea structure
            assert forall |j: nat| 0 <= j && j < self.ghost_state@.ptrs.len() implies self.is_node_wf(descs, descs_len, j) by {
                assert(j < i_witness ==> self.is_node_wf(descs, descs_len, j)) by {
                    assert(old(self).is_node_wf(descs, descs_len, j));
                }
                assert(i_witness < j ==> self.is_node_wf(descs, descs_len, j)) by {
                    assert(old(self).is_node_wf(descs, descs_len, j + 1));
                }
            }
        }

        Tracked(pointsto)
    }

    // pre-condition: page is not in the fa. self.wf()
    // post-condition:
    //  page is in the fa,
    //  self.wf(),
    //  zone_owned => all elements in fa has Tag::ZoneOwned.
    // !zone_owned => all elements in fa has Tag::InUsed.
    fn push(
        &mut self,
        Tracked(descs): Tracked<&[PageDescriptor]>,
        Ghost(descs_len): Ghost<nat>,
        page: &'static PageDescriptor,
        Tracked(pts): Tracked<PointsToNodes>,
        zone_owned: bool,
    )
        requires
            old(self).wf(descs, descs_len),
            pts.wf(page),
            page.wf(),
            pts.log_size() as int == old(self).ghost_state@.order.into_int(),
            pts@.is_some(),
            exists|i: nat| descs[i as int] == *page && i + ((1 as usize) << (pts.log_size() as usize)) < descs_len
        ensures
            self.wf(descs, descs_len),
            self.ghost_state@.order == old(self).ghost_state@.order,
            self.ghost_state@.ptrs.len() == old(self).ghost_state@.ptrs.len() + 1,
    {
        let tracked mut pts = pts;
        let head = self.head.take();
        let mut guard = page.get();
        let tracked mut perm = pts.take_perm(page);
        guard.set_node(Tracked(&mut perm), Node {
            next: head,
            prev: None,
        });
        proof {
            pts.restore_perm(page, perm);
        }
        if zone_owned {
            guard.set_tag(Tag::ZoneOwned);
        }
        if let Some(head) = head {
            assert(old(self).is_node_wf(descs, descs_len, 0));
            let tracked mut pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(0);
            let tracked mut perm = pointsto.take_perm(self.ghost_state@.ptrs[0]);
            head.get().set_node_prev(Tracked(&mut perm), Some(page));
            proof {
                pointsto.restore_perm(self.ghost_state@.ptrs[0], perm);
                self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, pointsto);
            }
        }
        self.head = Some(page);

        proof {
            // 1. Update `ptrs`
            self.ghost_state.borrow_mut().update_ptrs(seq![page].add(self.ghost_state@.ptrs));

            // 2. Shift indices of `points_to_map`
            let ghost key_map = Map::<nat, nat>::new(
                |j: nat| 1 <= j && j < self.ghost_state@.ptrs.len(),
                |j: nat| (j - 1) as nat
            );
            assert forall |j: nat| key_map.dom().contains(j) implies self.ghost_state@.points_to_map.dom().contains(key_map.index(j)) by {
                assert(old(self).is_node_wf(descs, descs_len, (j - 1) as nat));
            }
            self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(key_map);

            // 3. Add a new `PointsToNodes` resource and restore well-formedness condition
            self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, pts);
            assert forall |j: nat| 1 <= j && j < self.ghost_state@.ptrs.len() implies self.is_node_wf(descs, descs_len, j) by {
                assert(old(self).is_node_wf(descs, descs_len, (j - 1) as nat));
            }
        }
    }

    // pre, post condition: self.wf().
    fn pop(&mut self, Tracked(descs): Tracked<&[PageDescriptor]>, Ghost(descs_len): Ghost<nat>) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            old(self).wf(descs, descs_len),
        ensures
            self.wf(descs, descs_len),
            self.ghost_state@.order == old(self).ghost_state@.order,
            match ret {
                Some((desc, pts)) => {
                    &&& self.ghost_state@.ptrs.len() + 1 == old(self).ghost_state@.ptrs.len()
                    &&& desc.wf()
                    &&& pts@.wf(desc)
                    &&& pts@.log_size() as int == self.ghost_state@.order.into_int()
                    &&& pts@@.is_some()
                    &&& exists|i: nat| descs[i as int] == *desc && i + ((1 as usize) << (pts@.log_size() as usize)) < descs_len
                }
                None => self.ghost_state@.ptrs.len() == old(self).ghost_state@.ptrs.len() && self.ghost_state@.ptrs.len() == 0,
            }
    {
        let head = self.head?;
        assert(self.is_node_wf(descs, descs_len, 0));
        let pointsto = unsafe { self.remove(Tracked(descs), Ghost(descs_len), head.get()) };
        Some((head, pointsto))
    }
}

pub struct Cache {
    pub fa: FreeArea,
    pub size: usize,
    pub order: Order,
}

impl Cache {
    pub open spec fn wf(&self, descs: &[PageDescriptor], descs_len: nat) -> bool {
        &&& self.fa.wf(descs, descs_len)
        &&& self.fa.ghost_state@.order == self.order
        &&& self.order.into_int() <= 3
        &&& self.size as nat == self.fa.ghost_state@.ptrs.len()
        &&& descs_len < MAX_DESCRIPTOR_COUNT
    }

    fn get(&mut self, allocator: &ZoneAllocator) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            old(self).wf(allocator.descs.descs, allocator.descs.descs_len@),
            allocator.wf(),
        ensures
            self.wf(allocator.descs.descs, allocator.descs.descs_len@),
            self.order == old(self).order,
            match ret {
                Some(v) => {
                    &&& v.0.wf()
                    &&& v.1@.wf(v.0)
                    &&& v.1@.log_size() as int == self.order.into_int()
                    &&& v.1@@.is_some()
                    &&& exists|i: nat| allocator.descs.descs[i as int] == *v.0 && i + ((1 as usize) << (v.1@.log_size() as usize)) < allocator.descs.descs_len@
                }
                None => true,
            }
    {
        if self.size == 0 {
            if let Some((page, pointsto)) = unsafe { allocator.get_page_buddy(Order::Order8) } {
                let ghost page_idx = choose|i: nat|
                        allocator.descs.descs[i as int] == *page &&
                        i + ((1 as usize) << (pointsto@.log_size() as usize)) < allocator.descs.descs_len@;
                let mut guard = unsafe { page.get() };

                assume(match guard.lock_acc@@.value {
                    Some(v) => match v@@.value {
                        Some(c) => is_variant(c.info, "head"),
                        None => false,
                    }
                    None => false,
                });
                guard.set_common_info_head_order(self.order);
                let Tracked(pointsto) = pointsto;
                let step = 1 << self.order.into_usize();
                let pfn = allocator.descs.indexed_ref(page, Ghost(page_idx)).unwrap().frame_index();

                assert(pfn as nat == page_idx);
                assert(pointsto.wf(&allocator.descs.descs[pfn as int]));
                assert(self.order.into_int() <= pointsto.log_size());
                assert(pfn as nat + ((1 as usize) << (pointsto.log_size() as usize)) < allocator.descs.descs_len@);
                let tracked mut pointsto_seq = pointsto.resize(&allocator.descs.descs, allocator.descs.descs_len@, pfn as nat, self.order.into_int() as nat);
                assert(pointsto_seq.len() == ((1 as usize) << ((pointsto.log_size() - self.order.into_int()) as usize)));
                let tracked pointsto;
                proof {
                    // FIXME: Verus does not support reasoning about `<<` for usize
                    assume(pointsto_seq.len() != 0);
                    let tracked x = seq_split_front(pointsto_seq);
                    pointsto = x.0;
                    pointsto_seq = x.1;
                }

                guard.drop();

                // FIXME: Verus does not support reasoning about `<<` for usize
                assume(page_idx + ((1 as usize) << (pointsto.log_size() as usize)) < allocator.descs.descs_len@);
                unsafe { self.fa.push(Tracked(allocator.descs.descs), Ghost(allocator.descs.descs_len@), page, Tracked(pointsto), false) }

                let mut iter_idx: usize = 1 << (Order::Order8.into_usize() - self.order.into_usize()) - 1;
                // FIXME: Verus does not support reasoning about `<<` for usize
                assume(1 <= step && step <= 8);
                assume(pointsto_seq.len() == iter_idx as nat);
                let mut pfn_iter = pfn + step;

                // Prepare loop invariant
                assert forall|j: nat| j < pointsto_seq.len() implies pointsto_seq[j as int].wf(&allocator.descs.descs[pfn_iter + step * j]) by {
                    assert(pointsto_seq[j as int].wf(&allocator.descs.descs[pfn + step * (j + 1)]));
                    assert(step * (j + 1) == step * j + step) by(nonlinear_arith);
                }

                // Verus does not allow using the `step_by`
                // for pfn in (pfn + step..pfn + (1 << (Order::Order8 as usize))).step_by(step) {
                while 1 <= iter_idx
                    invariant
                        self.order == old(self).order,
                        self.fa.ghost_state@.order == self.order,
                        allocator.wf(),
                        self.fa.wf(&allocator.descs.descs, allocator.descs.descs_len@),
                        pointsto_seq.len() == iter_idx as nat,
                        0 <= iter_idx,
                        pointsto_seq.len() + self.fa.ghost_state@.ptrs.len() == ((1 as usize) << ((Order::Order8.into_int() - self.order.into_int()) as usize)),
                        forall|j: nat| j < pointsto_seq.len() ==> pointsto_seq[j as int].log_size() == self.order.into_int() as nat,
                        forall|j: nat| j < pointsto_seq.len() ==> pointsto_seq[j as int].wf(&allocator.descs.descs[pfn_iter + step * j]),
                        forall|j: nat| j < pointsto_seq.len() ==> pointsto_seq[j as int]@.is_some(),
                {
                    // FIXME: Verus does not support reasoning about `<<` for usize
                    assume(0 <= pfn_iter && pfn_iter < allocator.descs.descs_len@ - step);
                    let new_leader = allocator.descs.try_from_index(pfn_iter).unwrap().inner();
                    let tracked mut pointsto;
                    {
                        let mut guard = unsafe { new_leader.get() };
                        //debug_assert_eq!(guard.tag(), Tag::TrailingPage);

                        guard.set_tag(Tag::InUsed);
                        guard.set_common_info_head(Head {
                            order: self.order,
                            #[cfg(not(feature = "single_coffer"))]
                            owner: get_runid_mrid(),
                        });
                        proof {
                            let tracked x = seq_split_front(pointsto_seq);
                            pointsto = x.0;
                            pointsto_seq = x.1;
                        }
                        assert(pointsto.wf(&guard.original));
                        let tracked mut perm = pointsto.take_perm(&guard.original);
                        guard.set_node(Tracked(&mut perm), Node {
                            next: None,
                            prev: None,
                        });
                        proof {
                            pointsto.restore_perm(&guard.original, perm);
                        }

                        let mut idx: usize = 1;
                        while idx < step
                            invariant
                                allocator.wf(),
                                0 <= pfn_iter && pfn_iter < allocator.descs.descs_len@ - step,
                        {
                            unsafe {
                                let mut guard = allocator
                                    .descs
                                    .try_from_index(pfn_iter + idx)
                                    .unwrap()
                                    .inner()
                                    .get();
                                guard.set_common_info_compound(Compound { head: new_leader });
                            }
                        }
                        guard.drop();
                    }

                    assert(allocator.descs.descs[pfn_iter as int] == new_leader);
                    assert(pfn_iter + ((1 as usize) << (pointsto.log_size() as usize)) < allocator.descs.descs_len@) by {
                        assert(pointsto.log_size() == self.order.into_int() as nat);
                        // FIXME: Verus does not support reasoning about `<<` for usize
                        assume(((1 as usize) << (pointsto.log_size() as usize)) == step);
                    }
                    unsafe { self.fa.push(Tracked(allocator.descs.descs), Ghost(allocator.descs.descs_len@), new_leader, Tracked(pointsto), false) }

                    // Loop invariant for the next iteration
                    assert forall|j: nat| j < pointsto_seq.len() implies pointsto_seq[j as int].wf(&allocator.descs.descs[(pfn_iter + step) + step * j]) by {
                        assert(pointsto_seq[j as int].wf(&allocator.descs.descs[pfn_iter + step * (j + 1)]));
                        assert(step * (j + 1) == step * j + step) by(nonlinear_arith);
                    }

                    pfn_iter = pfn_iter + step;
                    iter_idx = iter_idx - 1;
                }

                self.size = 1 << (Order::Order8.into_usize() - self.order.into_usize());
            }
        }
        if let Some(o) = self.fa.pop(Tracked(allocator.descs.descs), Ghost(allocator.descs.descs_len@)) {
            self.size = self.size - 1;
            Some(o)
        } else {
            None
        }
    }

    fn put(
        &mut self,
        allocator: &ZoneAllocator,
        page: &'static PageDescriptor,
        Tracked(pointsto): Tracked<PointsToNodes>,
    ) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            old(self).wf(allocator.descs.descs, allocator.descs.descs_len@),
            allocator.wf(),
            page.wf(),
            pointsto.wf(page),
            pointsto@.is_some(),
            pointsto.log_size() as int == old(self).order.into_int(),
            exists|i: nat| allocator.descs.descs[i as int] == *page && i + ((1 as usize) << (pointsto.log_size() as usize)) < allocator.descs.descs_len@,
        ensures
            self.wf(allocator.descs.descs, allocator.descs.descs_len@),
            self.order == old(self).order,
            match ret {
                Some(v) => {
                    &&& v.0 == page
                    &&& v.1@ === pointsto
                }
                None => true,
            }
    {
        if self.size > 256 {
            Some((page, Tracked(pointsto)))
        } else {
            unsafe {
                let mut guard = page.get();
                assume(match guard.lock_acc@@.value {
                    Some(v) => match v@@.value {
                        Some(c) => is_variant(c.info, "head"),
                        None => false,
                    }
                    None => false,
                });
                let order = guard.borrow_common().info.head.order;
                //debug_assert_eq!(order, self.order);
                //debug_assert_eq!(guard.tag(), Tag::InUsed);

                let tracked mut pointsto = pointsto;
                guard.zeroing(Tracked(&mut pointsto));
                let tracked mut perm = pointsto.take_perm(page);
                guard.set_node(Tracked(&mut perm), Node {
                    next: None,
                    prev: None,
                });
                proof {
                    pointsto.restore_perm(page, perm);
                }
                guard.drop();

                self.fa.push(Tracked(allocator.descs.descs), Ghost(allocator.descs.descs_len@), page, Tracked(pointsto), false);

                self.size = self.size + 1;
                allocator
                    .available_pages
                    .fetch_add(1 << order.into_usize(), Ordering::Relaxed);
            }
            None
        }
    }
}

/// Zone allocator.
pub struct ZoneAllocator {
    /// The starting address of the zone. (inclusive)
    pub start_addr: usize,
    /// The end address of the zone. (exclusive)
    pub end_addr: usize,
    /// total pages spanned by the zone.
    pub _total_pages: AtomicUsize,
    /// available pages in the zone. (freed)
    pub available_pages: AtomicUsize,
    /// free areas of diffrent size.
    pub free_area: [LockWithSpec<FreeArea>; Order::MAX_ORDER as usize + 1],
    pub descs: PageDescriptors,
    pub deferred_frees: Option<(
        Sender<(&'static PageDescriptor, Tracked<PointsToNodes>)>,
        Receiver<(&'static PageDescriptor, Tracked<PointsToNodes>)>,
    )>,
    #[cfg(feature = "trace_zone")]
    pub tracer: tracer::Tracer<0x100000>,
}

} // verus!

unsafe impl Sync for ZoneAllocator {}

per_cpu!(
    static mut ORDER0_CACHE: Cache = Cache {
        fa: FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()),
        size: 0,
        order: Order::Order0,
    };
    static mut ORDER1_CACHE: Cache = Cache {
        fa: FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()),
        size: 0,
        order: Order::Order1,
    };
    static mut ORDER2_CACHE: Cache = Cache {
        fa: FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()),
        size: 0,
        order: Order::Order2,
    };
    static mut ORDER3_CACHE: Cache = Cache {
        fa: FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()),
        size: 0,
        order: Order::Order3,
    };
);

pub const MAX_DEFERRED_FREE: usize = 0x200000 / 8;

verus! {

#[cfg(not(feature = "single_coffer"))]
#[inline]
#[verifier::external_body]
// Verus does not support getting constant values
const fn get_runid_mrid() -> crate::monitor::RunId {
    crate::monitor::RunId::MRID
}

impl ZoneAllocator {
    pub open spec fn fa_spec(&self, fa: &LockWithSpec<FreeArea>, order_as_int: int) -> bool {
        &&& fa.wf()
        &&& forall|v| fa.inv(v) <==> (v.wf(self.descs.descs, self.descs.descs_len@) && v.ghost_state@.order.into_int() == order_as_int)
    }

    // Note: Verus does not support constant values.
    // "The verifier does not yet support the following Rust feature: associated constants"
    // So we use `Order::Order11` instead of `Order::MAX_ORDER`.
    pub open spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i && i < Order::Order11.into_int() + 1 ==> self.fa_spec(&self.free_area[i], i)
        &&& self.descs.wf()
    }

    #[inline]
    #[verifier::external_body]
    pub fn channel_push_spec(
        &self,
        inner: &ChannelInner<(&'static PageDescriptor, Tracked<PointsToNodes>)>,
        pg: &'static PageDescriptor,
        pts: Tracked<PointsToNodes>,
    ) -> (ret: Result<(), (&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
            pg.wf(),
            pts@.wf(pg),
            pts@@.is_some(),
            exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@,
        ensures
            match ret {
                Ok(_) => true,
                Err(v) => v.0 == pg && v.1 == pts,
            }
    {
        inner.push((pg, pts), |th| unsafe {
            th.unpark_to({
                #[cfg(not(feature = "single_coffer"))]
                {
                    &*crate::monitor::monitor_task::MTASK.as_ptr()
                }
                #[cfg(feature = "single_coffer")]
                {
                    crate::coffer::coffer()
                }
            })
        })
    }

    #[inline]
    #[verifier::external_body]
    pub fn channel_pop_spec(
        &self,
        inner: &ChannelInner<(&'static PageDescriptor, Tracked<PointsToNodes>)>,
    ) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
        ensures
            match ret {
                Some((pg, pts)) => {
                    &&& pg.wf()
                    &&& pts@.wf(pg)
                    &&& pts@@.is_some()
                    &&& exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@
                }
                None => true,
            }
    {
        inner.pop(|_| unreachable!())
    }

    #[inline]
    #[verifier::external_body]
    pub fn set_descriptor(&mut self, base: usize, descs: &'static mut [PageDescriptor])
    {
        #[cfg(feature = "ondemand_mm")]
        {
            self.descs = PageDescriptors {
                descs,
                base,
                tail: AtomicUsize::new(0),
            };
        }
        #[cfg(not(feature = "ondemand_mm"))]
        {
            self.descs = PageDescriptors { descs, base, descs_len: Ghost::assume_new() };
            for (i, desc) in self.descs.descs.iter().enumerate() {
                let mut guard = desc.get();
                guard.set_common_addr(Virtual::new(base + i * 0x1000).unwrap());
                guard.set_tag(Tag::InUsed);
            }
        }
    }

    fn restat(&mut self, start: usize, end: usize)
        requires
            min(old(self).start_addr as int, start as int) <= max(old(self).end_addr as int, end as int),
            start <= end,
            max(old(self).end_addr as int, end as int) < MAX_ADDR,
        ensures
            self.free_area == old(self).free_area,
            self.descs == old(self).descs,
            self.deferred_frees == old(self).deferred_frees,
    {
        if self.start_addr > start {
            // extend start
            self.start_addr = start;
        }
        if self.end_addr < end {
            // extend end
            self.end_addr = end;
        }
        // recalculate total pages
        self._total_pages = AtomicUsize::new((self.end_addr - self.start_addr + 1) >> PAGE_SHIFT);

        self.available_pages
            .fetch_add((end - start) >> PAGE_SHIFT, Ordering::Relaxed);
    }

    fn split_upper_order(
        &self,
        req_order: Order,
    ) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>, &'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
        ensures
            match ret {
                Some(v) => {
                    &&& v.0.wf()
                    &&& v.1@.wf(v.0)
                    &&& v.1@.log_size() == req_order.into_int() as nat
                    &&& v.1@@.is_some()
                    &&& v.2.wf()
                    &&& v.3@.wf(v.2)
                    &&& v.3@.log_size() == req_order.into_int() as nat
                    &&& v.3@@.is_some()
                    &&& exists|i: nat|
                            #[trigger]
                            self.descs.descs[i as int] == *v.0 && 
                            self.descs.descs[i as int + ((1 as usize) << (req_order.into_int() as usize))] == *v.2 &&
                            i + ((1 as usize) << (req_order.into_int() as usize)) + ((1 as usize) << (req_order.into_int() as usize)) < self.descs.descs_len@
                }
                None => true,
            }
    {
        let norder = req_order.get_next_order()?;
        let (page, Tracked(pointsto)) = self.get_page_with_pin(norder)?;
        let ghost page_idx = choose|i: nat| self.descs.descs[i as int] == page && i + ((1 as usize) << (norder.into_int() as usize)) < self.descs.descs_len@;
        assert(0 <= page_idx && page_idx < self.descs.descs_len@);
        // FIXME: Verus does not support reasoning about `<<` for usize
        assume(((1 as usize) << (norder.into_int() as usize)) == ((1 as usize) << (req_order.into_int() as usize)) + ((1 as usize) << (req_order.into_int() as usize)));

        // Change the leader's order.
        let mut guard = page.get();
        assume(match guard.lock_acc@@.value {
            Some(v) => match v@@.value {
                Some(c) => is_variant(c.info, "head"),
                None => false,
            }
            None => false,
        });
        guard.set_common_info_head_order(req_order);
        guard.drop();

        // Build second leader.
        let next_leader_pfn = {
            let fidx = self.descs.indexed_ref(page, Ghost(page_idx)).unwrap().frame_index();
            let shift_amount = req_order.into_usize();
            let add_val = 1 << shift_amount;
            assert(0 <= fidx && fidx < MAX_DESCRIPTOR_COUNT);
            assert(0 <= shift_amount && shift_amount <= 11);
            // FIXME: Verus does not support reasoning about `<<` for `usize`
            assume(0 <= add_val && add_val <= 10000);
            fidx + add_val
        };
        assert(next_leader_pfn == page_idx + ((1 as usize) << (req_order.into_int() as usize)));
        assert(next_leader_pfn < self.descs.descs_len@);
        let new_leader = self.descs.try_from_index(next_leader_pfn).unwrap().inner();

        assert(pointsto.wf(&self.descs.descs[page_idx as int]));
        assert(descs_len_wf(self.descs.descs, self.descs.descs_len@));
        assert(pointsto.log_size() != 0) by {
            assert(req_order != Order::Order11);
        }
        assert(page_idx + ((1 as usize) << ((pointsto.log_size() - 1) as usize)) < self.descs.descs_len@);
        let tracked mut pointsto = pointsto.split(self.descs.descs, self.descs.descs_len@, page_idx);
        let tracked mut pts_l;
        let tracked mut pts_r;
        proof {
            pts_l = pointsto.0;
            pts_r = pointsto.1;
        }
        assert(pts_r.wf(new_leader));

        let mut guard = new_leader.get();
        // debug_assert_eq!(guard.tag(), Tag::TrailingPage);

        guard.set_tag(Tag::InUsed);
        guard.set_common_info_head(Head {
            order: req_order,
            #[cfg(not(feature = "single_coffer"))]
            owner: get_runid_mrid(),
        });
        let tracked mut perm = pts_r.take_perm(new_leader);
        assert(perm@.pcell == new_leader.node.id());
        assert(new_leader == guard.original);
        guard.set_node(Tracked(&mut perm), Node {
            next: None,
            prev: None,
        });
        proof {
            pts_r.restore_perm(new_leader, perm);
        }
        guard.drop();

        #[verifier::no_auto_loop_invariant]
        for idx in 1..(1 << req_order.into_usize())
            invariant
                self.wf()
        {
            // FIXME: Verus does not support reasoning about `<<` with usize type
            assume(next_leader_pfn + idx < self.descs.descs_len@);
            let mut guard = self
                .descs
                .try_from_index(next_leader_pfn + idx)
                .unwrap()
                .inner()
                .get();
            guard.set_common_info_compound(Compound { head: new_leader });
        }

        assert(pts_l.wf(page));
        assert(pts_r.wf(new_leader));
        assert(pts_l.log_size() == req_order.into_int() as nat);
        assert(pts_r.log_size() == req_order.into_int() as nat);
        Some((page, Tracked(pts_l), new_leader, Tracked(pts_r)))
    }

    fn get_page_buddy(&self, order: Order) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
        ensures
            match ret {
                Some(v) => {
                    &&& v.0.wf()
                    &&& v.1@.wf(v.0)
                    &&& v.1@.log_size() == order.into_int()
                    &&& v.1@@.is_some()
                    &&& exists|i: nat| self.descs.descs[i as int] == *v.0 && i + ((1 as usize) << (v.1@.log_size() as usize)) < self.descs.descs_len@
                }
                None => true,
            }
    {
        assert(self.fa_spec(&self.free_area[order.into_int()], order.into_int()));
        let (mut perm, guard) = self.free_area[order.into_usize()].acquire();
        assert(match perm@@.value {
            Some(v) => v.wf(self.descs.descs, self.descs.descs_len@) && v.ghost_state@.order.into_int() == order.into_int(),
            None => false,
        });
        let fa = self.free_area[order.into_usize()].data.borrow(Tracked(perm.borrow()));
        if fa.head.is_none() {
            let (a, apts, b, bpts) = self.split_upper_order(order)?;

            let mut fa = self.free_area[order.into_usize()].data.take(Tracked(&mut perm.borrow_mut()));
            fa.push(Tracked(self.descs.descs), Ghost(self.descs.descs_len@), a, apts, true);
            self.free_area[order.into_usize()].data.put(Tracked(&mut perm.borrow_mut()), fa);
            self.free_area[order.into_usize()].release(perm);
            guard.drop();

            Some((b, bpts))
        } else {
            let mut fa = self.free_area[order.into_usize()].data.take(Tracked(&mut perm.borrow_mut()));
            let res = fa.pop(Tracked(self.descs.descs), Ghost(self.descs.descs_len@));
            self.free_area[order.into_usize()].data.put(Tracked(&mut perm.borrow_mut()), fa);
            self.free_area[order.into_usize()].release(perm);
            guard.drop();

            res
        }
    }

    // Both object should be zone owned and not in the linked list.
    fn merge<'a>(
        &'a self,
        mut order: Order,
        mut pg: PageDescriptorIndex<'a>,
        mut pg_pts: Tracked<PointsToNodes>,
    ) -> (ret: (PageDescriptorIndex<'a>, Tracked<PointsToNodes>, Order))
        requires
            self.wf(),
            pg.wf(),
            self.descs == pg.descs,
            pg_pts@.wf(&self.descs.descs[pg.index as int]),
            pg_pts@.log_size() as int == order.into_int(),
            pg_pts@@.is_some(),
            pg.index as nat + ((1 as usize) << (order.into_int() as usize)) < self.descs.descs_len@,
        ensures
            ret.0.wf(),
            self.descs == ret.0.descs,
            ret.1@.wf(&self.descs.descs[ret.0.index as int]),
            ret.1@.log_size() as int == ret.2.into_int(),
            ret.1@@.is_some(),
            ret.0.index as nat + ((1 as usize) << (ret.2.into_int() as usize)) < self.descs.descs_len@,
// ensures
    // pd.wf(),
    // ret.0.order == ret.1,
    // &&&(||| order == maxorder => ret.1.order
    // ||| ret.1.order == order + 1 // merged
    // ||| ret.1.order == order // not merged
    // )
    {
        let mut addr = pg.copy().addr();
        proof {
            order_size_range(order);
        }
        // Note: we use `Order::Order11` instead of `Order::MAX_ORDER` due to limitation of Verus.
        // Also note the following error message by Verus:
        // "error: The verifier does not yet support the following Rust feature: ==/!= for non smt equality types"
        // Hence, we compare the usize version of `order` with `Order::Order11` instead of direct
        // comparison between them.
        while order.into_usize() != Order::Order11.into_usize() && addr + order.size_with_spec() < self.end_addr
            invariant
                self.wf(),
                pg.wf(),
                self.descs == pg.descs,
                pg_pts@.wf(&self.descs.descs[pg.index as int]),
                pg_pts@.log_size() as int == order.into_int(),
                pg_pts@@.is_some(),
                pg.index as nat + ((1 as usize) << (order.into_int() as usize)) < self.descs.descs_len@,
                pg.is_addr(addr as int),
                0 <= addr && addr < MAX_ADDR,
                descr_addr_aligned(addr as int),
                0 <= order.size_spec() && order.size_spec() <= MAX_ORDER_SIZE,
        {
            let direction = trailing_zeros_spec(addr) - PAGE_SHIFT == order.into_usize();
            let merge_candidate_addr = if direction {
                checked_sub_spec(addr, order.size_with_spec())
            } else {
                checked_add_spec(addr, order.size_with_spec())
            };
            assert(match merge_candidate_addr {
                Some(merge_candidate) => descr_addr_aligned(merge_candidate as int),
                None => true,
            }) by {
                diff_by_order_size(addr as int, order);
            }

            let mut merge_pair = None;
            if let Some(merge_candidate) = merge_candidate_addr {
                if let Some(cand) = self.descs.try_from_addr(merge_candidate) {
                    // Here's the lock ordering is important to avoid deadlock.
                    // FreeArea.lock() => guard.lock()
                    assert(self.fa_spec(&self.free_area[order.into_int()], order.into_int()));
                    let (mut area_perm, area_guard) = self.free_area[order.into_usize()].acquire();
                    let cand_guard = cand.get();

                    match cand_guard.tag() {
                        Tag::ZoneOwned => {
                            if unsafe { cand_guard.borrow_common().info.head.order.into_usize() } == order.into_usize() {
                                let mut area = self.free_area[order.into_usize()].data.take(Tracked(&mut area_perm.borrow_mut()));
                                assume(exists|i: nat| 0 <= i && i < area.ghost_state@.ptrs.len() && area.ghost_state@.ptrs[i as int] == &cand_guard.original);
                                let cand_pts = area.remove(Tracked(&self.descs.descs), Ghost(self.descs.descs_len@), cand_guard);

                                self.free_area[order.into_usize()].data.put(Tracked(&mut area_perm.borrow_mut()), area);
                                self.free_area[order.into_usize()].release(area_perm);
                                area_guard.drop();

                                assert(cand_pts@.log_size() as int == order.into_int());
                                let ghost cand_idx = choose|i: nat|
                                    self.descs.descs[i as int] == cand_guard.original &&
                                    i + ((1 as usize) << (cand_pts@.log_size() as usize)) < self.descs.descs_len@;
                                proof {
                                    self.descs.index_unique(cand.index as nat, cand_idx);
                                    assert(cand.index as nat + ((1 as usize) << (order.into_int() as usize)) < self.descs.descs_len@);
                                }

                                merge_pair = if direction {
                                    Some((cand, pg.copy(), cand_pts))
                                } else {
                                    Some((pg.copy(), cand, cand_pts))
                                };
                            } else {
                                self.free_area[order.into_usize()].release(area_perm);
                                area_guard.drop();
                                return (pg, pg_pts, order);
                            }
                        }
                        _ => {
                            self.free_area[order.into_usize()].release(area_perm);
                            area_guard.drop();
                            return (pg, pg_pts, order);
                        }
                    }
                }
            }

            if let Some((leader, next, pts)) = merge_pair {
                let leader_copy = leader.copy();
                let mut leader_guard = leader_copy.get();
                let mut next_guard = next.get();
                let next_order = order.get_next_order().unwrap();
                assert(next_order.into_int() == order.into_int() + 1);
                let (Tracked(leader_pts), Tracked(next_pts)) = if direction {
                    (pts, pg_pts)
                } else {
                    (pg_pts, pts)
                };

                // Merge the two `PointstoNodes` resources
                let tracked mut leader_pts = leader_pts;
                let tracked mut next_pts = next_pts;
                proof {
                    if direction {
                        assert(leader.is_addr(addr as int - order.size_spec()));
                        assert(next.is_addr(addr as int));
                        leader.addr_diff_by_order(&next, addr as int - order.size_spec(), order);
                        leader_pts = leader_pts.merge(next_pts, &self.descs.descs, self.descs.descs_len@, leader.index as nat);
                    } else {
                        assert(leader.is_addr(addr as int));
                        assert(next.is_addr(addr as int + order.size_spec()));
                        leader.addr_diff_by_order(&next, addr as int, order);
                        leader_pts = leader_pts.merge(next_pts, &self.descs.descs, self.descs.descs_len@, leader.index as nat);
                    }
                    // FIXME: Verus does not support reasoning about `<<` for usize
                    assume(((1 as usize) << (next_order.into_int() as usize)) == ((1 as usize) << (order.into_int() as usize)) + ((1 as usize) << (order.into_int() as usize)));
                    assert(leader.index as nat + ((1 as usize) << (next_order.into_int() as usize)) < self.descs.descs_len@);
                }

                leader_guard.set_common_info_head(Head {
                    order: next_order,
                    #[cfg(not(feature = "single_coffer"))]
                    owner: get_runid_mrid(),
                });
                // Set trailing pages' head.
                let leader_desc = leader.copy().inner();
                next_guard.set_tag(Tag::TrailingPage);
                next_guard.set_common_info_compound(Compound {
                    head: leader_desc,
                });
                next_guard.drop();
                let mut idx: usize = 1;
                let bound: usize = 1 << (next_order.into_usize() - 1);
                while idx < bound
                    invariant
                        self.wf(),
                        next.index + bound < self.descs.descs_len@,
                {
                    let mut guard = self
                        .descs
                        .try_from_index(next.frame_index() + idx)
                        .unwrap()
                        .inner()
                        .get();
                    guard.set_common_info_compound(Compound {
                        head: leader_desc,
                    });
                }

                assume(leader_guard.wf());
                leader_guard.drop();

                // Merged. Try to merge next.
                order = next_order;
                addr = leader.addr();
                pg = leader;
                pg_pts = Tracked(leader_pts);

                proof {
                    order_size_range(order);
                }
            } else {
                break;
            }
        }
        (pg, pg_pts, order)
    }

    fn free_page(&self, pg: &'static PageDescriptor, pts: Tracked<PointsToNodes>, order: Order)
        requires
            self.wf(),
            pg.wf(),
            pts@.wf(pg),
            pts@.log_size() as int == order.into_int(),
            pts@@.is_some(),
            exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@,
    {
        let ghost pg_idx = choose|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@;
        let pg = self.descs.indexed_ref(pg, Ghost(pg_idx)).unwrap();
        let (pg, pg_pts, order) = self.merge(order, pg, pts);

        assert(self.fa_spec(&self.free_area[order.into_int()], order.into_int()));

        let (mut perm, guard) = self.free_area[order.into_usize()].acquire();
        let mut fa = self.free_area[order.into_usize()].data.take(Tracked(&mut perm.borrow_mut()));
        fa.push(Tracked(&self.descs.descs), Ghost(self.descs.descs_len@), pg.inner(), pg_pts, true);
        self.free_area[order.into_usize()].data.put(Tracked(&mut perm.borrow_mut()), fa);
        self.free_area[order.into_usize()].release(perm);

        guard.drop();
    }

    fn free_work(&self, pg: &'static PageDescriptor, Tracked(pts): Tracked<PointsToNodes>)
        requires
            self.wf(),
            pg.wf(),
            pts.wf(pg),
            pts@.is_some(),
            exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts.log_size() as usize)) < self.descs.descs_len@,
    {
        let tracked mut pts = pts;
        let mut guard = pg.get();
        assume(match guard.lock_acc@@.value {
            Some(v) => match v@@.value {
                Some(c) => is_variant(c.info, "head"),
                None => false,
            }
            None => false,
        });
        let order = unsafe { guard.borrow_common().info.head.order };
        assume(pts.log_size() as int == order.into_int());
        unsafe {
            guard.zeroing(Tracked(&mut pts));
        }
        let tracked mut perm = pts.take_perm(pg);
        guard.set_node(Tracked(&mut perm), Node {
            next: None,
            prev: None,
        });
        proof {
            pts.restore_perm(pg, perm);
        }
        guard.drop();
        self.free_page(pg, Tracked(pts), order);
        self.available_pages
            .fetch_add(1 << order.into_usize(), Ordering::Relaxed);
    }

    // no invariante holds.
    // Note: Verus currently does not support
    //       (1) Accessing global mutable resource `ALLOCATOR`
    //       (2) Use of string literal "mfreed"
    #[verifier::external_body]
    pub(crate) fn start_deferred_free_work() {
        #[cfg(not(feature = "free_daemon_off"))]
        {
            let (tx, rx) = crate::service::threading::channel::channel(MAX_DEFERRED_FREE);
            unsafe { ALLOCATOR.deferred_frees = Some((tx, rx.clone())); }
            crate::runtime::ktask::start_ktask("mfreed", move || {
                info!("mfreed is started.",);
                loop {
                    let (pg, pts) = rx.recv().unwrap();
                    unsafe { ALLOCATOR.free_work(pg, pts); }
                }
                // SAFETY: this threads runs on MTASK.
            })
        }
    }

    fn get_page(
        &self,
        order: Order,
        p: impl PreemptDisabled,
    ) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
        ensures
            match ret {
                Some(v) => {
                    &&& v.0.wf()
                    &&& v.1@.wf(v.0)
                    &&& v.1@.log_size() == order.into_int() as nat
                    &&& v.1@@.is_some()
                    &&& exists|i: nat| self.descs.descs[i as int] == v.0 && i + ((1 as usize) << (order.into_int() as usize)) < self.descs.descs_len@
                }
                None => true,
            }
    {
        match order {
            Order::Order0 | Order::Order1 | Order::Order2 | Order::Order3 => per_cpu_cache_do_get(self, order, p),
            _ => {
                preemptdisabled_drop(p);
                self.get_page_buddy(order)
            }
        }
    }

    #[inline]
    fn get_page_with_pin(&self, order: Order) -> (ret: Option<(&'static PageDescriptor, Tracked<PointsToNodes>)>)
        requires
            self.wf(),
        ensures
            match ret {
                Some(v) => {
                    &&& v.0.wf()
                    &&& v.1@.wf(v.0)
                    &&& v.1@.log_size() == order.into_int() as nat
                    &&& v.1@@.is_some()
                    &&& exists|i: nat| self.descs.descs[i as int] == v.0 && i + ((1 as usize) << (order.into_int() as usize)) < self.descs.descs_len@
                }
                None => true,
            }
    {
        self.get_page(order, current_get_pin())
    }

    fn put_page(&self, pg: &'static PageDescriptor, pts: Tracked<PointsToNodes>)
        requires
            self.wf(),
            pg.wf(),
            pts@.wf(pg),
            pts@@.is_some(),
            exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@,
    {
        let pin = current_get_pin();

        let guard = pg.get();
        assume(match guard.lock_acc@@.value {
            Some(v) => match v@@.value {
                Some(c) => is_variant(c.info, "head"),
                None => false,
            }
            None => false,
        });
        let order = unsafe { guard.borrow_common().info.head.order };
        assume(pts@.log_size() as int == order.into_int());
        guard.drop();
        if let Some((page, pointsto)) = match order {
            Order::Order0 | Order::Order1 | Order::Order2 | Order::Order3 => per_cpu_cache_do_put(self, pg, pts, order, pin),
            _ => {
                preemptdisabled_drop(pin);
                Some((pg, pts))
            }
        } {
            self.free_work(page, pointsto)
        }
    }

    /// Allocate a page.
    fn do_alloc_for(
        &self,
        order: Order,
        #[cfg(not(feature = "single_coffer"))] rid: crate::monitor::RunId,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
        p: impl PreemptDisabled,
    ) -> Option<&'static PageDescriptor>
        requires
            self.wf(),
    {
        let mut has_free_work = false;
        loop
            invariant
                self.wf(),
        {
            if let Some((pg, pointsto)) = self.get_page(order, &p) {
                self.available_pages
                    .fetch_sub(1 << order.into_usize(), Ordering::Relaxed);
                // Set ownership of returning page.
                #[cfg(not(feature = "single_coffer"))]
                {
                    let mut guard = pg.get();
                    assume(match guard.lock_acc@@.value {
                        Some(v) => match v@@.value {
                            Some(c) => is_variant(c.info, "head"),
                            None => false,
                        }
                        None => false,
                    });
                    guard.set_common_info_head_owner(rid);
                    guard.drop();
                }

                #[cfg(feature = "trace_zone")]
                inner.tracer.trace_alloc(pg.get().addr, caller);
                return Some(pg);
            } else if has_free_work {
                #[cfg(feature = "ondemand_mm")]
                return self.extend(order);
                #[cfg(not(feature = "ondemand_mm"))]
                return None;
            } else if let Some((_, rx)) = self.deferred_frees.as_ref() {
                let inner = rx.inner();
                loop
                    invariant
                        self.wf(),
                {
                    let case = match self.channel_pop_spec(inner) {
                        Some(n) => Some(n),
                        None if !inner.has_sender() => self.channel_pop_spec(inner),
                        None => None,
                    };
                    if let Some((pg, pts)) = case {
                        let guard = pg.get();
                        assume(match guard.lock_acc@@.value {
                            Some(v) => match v@@.value {
                                Some(c) => is_variant(c.info, "head"),
                                None => false,
                            }
                            None => false,
                        });
                        let pg_order = unsafe { guard.borrow_common().info.head.order };
                        guard.drop();
                        self.free_work(pg, pts);
                        if pg_order.into_usize() >= order.into_usize() {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }
            has_free_work = true;
        }
    }

    /// Deallocate the page.
    fn do_dealloc(
        &self,
        pg: &'static PageDescriptor,
        pts: Tracked<PointsToNodes>,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
    )
        requires
            self.wf(),
            pg.wf(),
            pts@.wf(pg),
            pts@@.is_some(),
            exists|i: nat| self.descs.descs[i as int] == *pg && i + ((1 as usize) << (pts@.log_size() as usize)) < self.descs.descs_len@,
    {
        let mut guard = pg.get();
        #[cfg(not(feature = "single_coffer"))]
        {
            assume(match guard.lock_acc@@.value {
                Some(v) => match v@@.value {
                    Some(c) => is_variant(c.info, "head"),
                    None => false,
                }
                None => false,
            });
            guard.set_common_info_head_owner(get_runid_mrid());
        }
        #[cfg(feature = "trace_zone")]
        let addr = guard.common.addr.into_usize();

        guard.drop();
        if let Some((chan, _)) = self.deferred_frees.as_ref() {
            let chan_inner = chan.inner();
            if let Err((pg, pts)) = self.channel_push_spec(chan_inner, pg, pts) {
                unsafe { self.put_page(pg, pts) }
            }
        } else {
            unsafe { self.put_page(pg, pts) }
        }

        #[cfg(feature = "trace_zone")]
        inner.tracer.trace_dealloc(addr, caller);
    }

    // we don't need to verify this.
    #[cfg(feature = "ondemand_mm")]
    fn extend(&self, order: Order) -> Option<&'static PageDescriptor> {
        let (ptail, mut ntail) = loop {
            let ptail = self.descs.tail.load(Ordering::Acquire);
            let mask = (1 << order as usize) - 1;
            let ntail = (ptail + (1 << order as usize) + mask) & !mask;
            if ntail >= self.descs.descs.len() {
                return None;
            } else if self
                .descs
                .tail
                .compare_exchange(ptail, ntail, Ordering::Acquire, Ordering::Acquire)
                .is_ok()
            {
                self.available_pages
                    .fetch_add(ntail - ptail, Ordering::Relaxed);
                break (ptail, ntail);
            }
        };

        let mut ret = None;
        while ptail < ntail {
            let order = Order::from_usize((ntail - ptail).ilog2() as usize).unwrap();

            let tail = ntail - (1 << order as usize);
            let head = &self.descs.descs[tail];
            let mut guard = head.get();
            guard.common.info.head = Head {
                order,
                #[cfg(not(feature = "single_coffer"))]
                owner: crate::monitor::RunId::monitor_rid(),
            };
            guard.common.addr = Virtual::new(self.descs.base + tail * 0x1000).unwrap();
            guard.common.tag = Tag::InUsed;
            *guard.get_private() = Node {
                next: None,
                prev: None,
            };
            drop(guard);
            (1..(1 << order as usize)).for_each(|idx| {
                let trail_page = &self.descs.descs[tail + idx];
                let guard = trail_page.get();
                guard.common.tag = Tag::TrailingPage;
                guard.common.info.compound = Compound { head };
                guard.common.addr = Virtual::new(self.descs.base + (tail + idx) * 0x1000).unwrap();
            });
            if ret.is_none() {
                ret = Some(head)
            } else {
                self.put_page(head);
            }
            ntail = tail;
        }
        ret
    }

    /// Foster the zone allocator.
    ///
    /// # Safety
    /// start ~ end must be usable physical address.
    #[link_section = ".init"]
    pub fn foster(&mut self, start: usize, end: usize, _state: &OnBoot)
        requires
            old(self).wf(),
            min(old(self).start_addr as int, round_up_to_page(start) as int) <= max(old(self).end_addr as int, round_down_to_page(end) as int),
            round_up_to_page(start) <= round_down_to_page(end),
            max(old(self).end_addr as int, round_down_to_page(end) as int) < MAX_ADDR,
            old(self).descs.base <= round_up_to_page(start),
            ((round_down_to_page(end) - old(self).descs.base) as usize) >> PAGE_SHIFT < old(self).descs.descs_len@,
        ensures
            self.wf(),
            self.free_area == old(self).free_area,
            self.descs == old(self).descs,
            self.deferred_frees == old(self).deferred_frees,
    {
        proof {
            round_up_down_property(start);
            round_up_down_property(end);
            assert(start < MAX_ADDR);
        }
        let (start, end) = ((start + PAGE_MASK) & !PAGE_MASK, end & !PAGE_MASK);
        self.restat(start, end);

        let mut cur = start;
        while cur < end
            invariant
                self.wf(),
                self.free_area == old(self).free_area,
                self.descs == old(self).descs,
                self.deferred_frees == old(self).deferred_frees,
                descr_addr_aligned(cur as int),
                descr_addr_aligned(end as int),
                self.descs.base <= cur,
                ((end - self.descs.base) as usize) >> PAGE_SHIFT < self.descs.descs_len@,
                end < MAX_ADDR,
        {
            let rem = end - cur;
            proof {
                aligned_min_diff(cur as int, end as int);
            }
            let corder = min_spec(
                match Order::fit_size(rem) {
                    Some(n) if n.size_with_spec() <= rem => n.into_usize(),
                    Some(n) => n.get_prev_order().unwrap().into_usize(),
                    None => Order::Order11.into_usize(),
                },
                trailing_zeros_spec(cur) - PAGE_SHIFT
            );

            // Make a head page.
            // FIXME: Verus does not support reasoning about `<<` for usize
            assume((1 as usize) << ((corder + PAGE_SHIFT) as usize) <= rem);
            assume(((cur - self.descs.base) as usize) >> PAGE_SHIFT < self.descs.descs_len@);
            let head_page = self
                .descs
                .try_from_index((cur - self.descs.base) >> PAGE_SHIFT)
                .unwrap();
            let mut guard = head_page.get();

            // Create a new `PointsToNodes` resource for the head page
            let tracked mut pts = PointsToNodes::assume_new();
            assume(pts.wf(&self.descs.descs[head_page.index as int]));
            assume(pts.log_size() == corder as nat);
            assume(pts@.is_some());

            // Write basic information
            guard.set_common_info_head(Head {
                order: Order::from_usize(corder).unwrap(),
                #[cfg(not(feature = "single_coffer"))]
                owner: get_runid_mrid(),
            });
            guard.set_common_addr(virtual_new_wrapper(cur));
            guard.set_tag(Tag::InUsed);
            let tracked mut perm = pts.take_perm(&self.descs.descs[head_page.index as int]);
            guard.set_node(Tracked(&mut perm), Node {
                next: None,
                prev: None,
            });
            proof {
                pts.restore_perm(&self.descs.descs[head_page.index as int], perm);
            }
            guard.zeroing(Tracked(&mut pts));
            guard.drop();

            // Make trailing pages.
            let head = head_page.inner();
            let mut idx: usize = 1;
            let mut bound: usize = 1 << corder;
            while idx < bound
                invariant
                    self.wf(),
                    self.descs.base <= cur,
                    (1 as usize) << ((corder + PAGE_SHIFT) as usize) <= rem,
                    ((end - self.descs.base) as usize) >> PAGE_SHIFT < self.descs.descs_len@,
                    cur < MAX_ADDR,
            {
                // FIXME: Verus does not support reasoning about `<<` for usize
                assume((((cur - self.descs.base) as usize) >> PAGE_SHIFT) + idx < self.descs.descs_len@);
                assume(bound <= 2048);
                let trail_page = self
                    .descs
                    .try_from_index(((cur - self.descs.base) >> PAGE_SHIFT) + idx)
                    .unwrap();
                let mut guard = trail_page.get();
                guard.set_tag(Tag::TrailingPage);
                guard.set_common_info_compound(Compound { head });
                guard.set_common_addr(virtual_new_wrapper(cur + idx * 0x1000));
                guard.drop();
            }

            // Put head page into free area.
            assert(self.fa_spec(&self.free_area[corder as int], corder as int));
            let (mut perm, guard) = self.free_area[corder].acquire();
            let mut fa = self.free_area[corder].data.take(Tracked(&mut perm.borrow_mut()));
            // FIXME: Verus does not support reasoning about `<<` for usize
            assume(exists|i: nat| self.descs.descs[i as int] == head && i + ((1 as usize) << (pts.log_size() as usize)) < self.descs.descs_len@);
            fa.push(Tracked(&self.descs.descs), Ghost(self.descs.descs_len@), head, Tracked(pts), true);
            self.free_area[corder].data.put(Tracked(&mut perm.borrow_mut()), fa);
            self.free_area[corder].release(perm);
            guard.drop();

            assert(descr_addr_aligned(cur + ((1 as usize) << ((corder + PAGE_SHIFT) as usize)))) by {
                let order =
                    if corder == 0 {
                        Order::Order0
                    } else if corder == 1 {
                        Order::Order1
                    } else if corder == 2 {
                        Order::Order2
                    } else if corder == 3 {
                        Order::Order3
                    } else if corder == 4 {
                        Order::Order4
                    } else if corder == 5 {
                        Order::Order5
                    } else if corder == 6 {
                        Order::Order6
                    } else if corder == 7 {
                        Order::Order7
                    } else if corder == 8 {
                        Order::Order8
                    } else if corder == 9 {
                        Order::Order9
                    } else if corder == 10 {
                        Order::Order10
                    } else {
                        Order::Order11
                    };
                assert(corder as int == order.into_int());
                assert(((1 as usize) << ((corder + PAGE_SHIFT) as usize)) == order.size_spec());
                diff_by_order_size(cur as int, order);
            }

            cur = cur + (1 << (corder + PAGE_SHIFT));
        }
    }

    #[cfg(feature = "ondemand_mm")]
    #[inline]
    pub unsafe fn init_slot(&mut self, idx: usize) {
        let desc = &self.descs.descs[idx];
        let guard = desc.get();
        guard.common.addr = Virtual::new(self.descs.base + idx * 0x1000).unwrap();
        guard.common.tag = Tag::InUsed;
        self.descs.tail.store(idx + 1, Ordering::Relaxed);
    }
}

} // verus!

#[cfg(not(feature = "single_coffer"))]
impl<G: crate::grants::OnMonitorCall + PreemptDisabled> ComponentGuard<G, ZoneAllocator> {
    /// Free all pages used by rid.
    /// ensures there is no pd for rid.
    pub(crate) fn free_memory_for(&self, rid: crate::monitor::RunId) {
        let mut index = 0;
        while index < self.descs.descs.len() {
            let mut desc = self.descs.try_from_index(index).unwrap();
            loop {
                let guard = desc.get();
                let common = guard.borrow_common();
                let fwd = match guard.tag() {
                    Tag::TrailingPage => {
                        let ndesc = self
                            .descs
                            .indexed_ref(unsafe { common.info.compound.head }, Ghost::assume_new())
                            .unwrap();
                        drop(guard);
                        desc = ndesc;
                        continue;
                    }
                    _ => unsafe { common.info.head.order.npages() },
                };
                if unsafe { common.info.head.owner.0 } == rid.0 {
                    drop(guard);
                    // TODO: How can we get `Tracked<PointsToNodes>` for this descriptor?
                    self.do_dealloc(
                        desc.inner(),
                        Tracked::assume_new(),
                        #[cfg(feature = "trace_zone")]
                        core::panic::Location::caller(),
                    );
                }
                index += fwd;
                break;
            }
        }
    }
}

// Followings does not require to verify as they are wrappers.
#[cfg(not(feature = "single_coffer"))]
impl<G: crate::grants::OnMonitorCall + PreemptDisabled> ComponentGuard<G, ZoneAllocator> {
    pub unsafe fn alloc_for(
        &self,
        order: Order,
        #[cfg(not(feature = "single_coffer"))] rid: crate::monitor::RunId,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
    ) -> Option<&'static PageDescriptor> {
        let Self { mcall, inner } = self;
        inner.do_alloc_for(
            order,
            #[cfg(not(feature = "single_coffer"))]
            rid,
            #[cfg(feature = "trace_zone")]
            caller,
            mcall,
        )
    }
    pub(crate) unsafe fn dealloc(
        &self,
        pg: &'static PageDescriptor,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
    ) {
        self.inner.do_dealloc(
            pg,
            Tracked::assume_new(),
            #[cfg(feature = "trace_zone")]
            caller,
        )
    }
}

#[cfg(feature = "single_coffer")]
impl ComponentGuard<ZoneAllocator> {
    pub unsafe fn alloc_for(
        &self,
        order: Order,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
    ) -> Option<&'static PageDescriptor> {
        self.inner.do_alloc_for(
            order,
            #[cfg(feature = "trace_zone")]
            caller,
            crate::service::threading::Current::get().pin(),
        )
    }
    pub unsafe fn dealloc(
        &self,
        pg: &'static PageDescriptor,
        #[cfg(feature = "trace_zone")] caller: &'static core::panic::Location<'static>,
    ) {
        self.inner.do_dealloc(
            pg,
            #[cfg(feature = "trace_zone")]
            caller,
        )
    }
}

static mut ALLOCATOR: ZoneAllocator = ZoneAllocator {
    start_addr: usize::MAX,
    end_addr: 0,
    _total_pages: AtomicUsize::new(0),
    available_pages: AtomicUsize::new(0),
    free_area: [
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
        LockWithSpec::new(FreeArea::empty(Ghost::assume_new(), Tracked::assume_new(), Ghost::assume_new()), Ghost::assume_new()),
    ],
    deferred_frees: None,
    descs: PageDescriptors {
        descs: &[],
        descs_len: Ghost::assume_new(),
        base: 0,
        #[cfg(feature = "ondemand_mm")]
        tail: AtomicUsize::new(0),
    },
    #[cfg(feature = "trace_zone")]
    tracer: tracer::Tracer::new(),
};

// This only returns readonly or owned reference of PageDescriptor.
// Therefore, we don't need monitorcall.
#[inline]
pub fn descs() -> &'static PageDescriptors {
    unsafe { &ALLOCATOR.descs }
}

#[inline]
#[cfg(not(feature = "single_coffer"))]
pub fn allocator<G: crate::grants::OnMonitorCall>(mcall: G) -> ComponentGuard<G, ZoneAllocator> {
    ComponentGuard {
        mcall,
        inner: unsafe { &mut *core::ptr::addr_of_mut!(ALLOCATOR) },
    }
}

#[inline]
#[cfg(feature = "single_coffer")]
pub fn allocator() -> ComponentGuard<ZoneAllocator> {
    ComponentGuard {
        inner: unsafe { &mut *core::ptr::addr_of_mut!(ALLOCATOR) },
    }
}
