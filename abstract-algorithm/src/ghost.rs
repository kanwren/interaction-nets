use std::cell::UnsafeCell;
use std::marker::PhantomData;

pub type InvariantLifetime<'a> = PhantomData<UnsafeCell<&'a ()>>;

pub struct GhostToken<'id> {
    _marker: InvariantLifetime<'id>,
}

#[repr(transparent)]
pub struct GhostCell<'id, T: ?Sized> {
    _marker: InvariantLifetime<'id>,
    value: UnsafeCell<T>,
}

impl<'id> GhostToken<'id> {
    pub fn with<R>(f: impl for<'new_id> FnOnce(GhostToken<'new_id>) -> R) -> R {
        f(GhostToken {
            _marker: PhantomData,
        })
    }
}

impl<'id, T> GhostCell<'id, T> {
    pub fn new(value: T) -> Self {
        GhostCell {
            _marker: PhantomData,
            value: UnsafeCell::new(value),
        }
    }

    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    pub fn replace<'a>(&'a self, value: T, token: &'a mut GhostToken<'id>) -> T {
        std::mem::replace(self.borrow_mut(token), value)
    }

    pub fn take<'a>(&'a self, token: &'a mut GhostToken<'id>) -> T where T: Default {
        self.replace(T::default(), token)
    }
}

impl<'id, T: ?Sized> GhostCell<'id, T> {
    pub fn as_ptr(&self) -> *mut T {
        self.value.get()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    pub fn from_mut(t: &mut T) -> &mut Self {
        // SAFETY: GhostCell<'id, T> has the same representation as T
        unsafe { std::mem::transmute(t) }
    }

    pub fn borrow<'a>(&'a self, _token: &'a GhostToken<'id>) -> &'a T {
        unsafe { &*self.value.get() }
    }

    pub fn borrow_mut<'a>(&'a self, _token: &'a mut GhostToken<'id>) -> &'a mut T {
        unsafe { &mut *self.value.get() }
    }
}

impl<'id, T> AsMut<T> for GhostCell<'id, T> {
    fn as_mut(&mut self) -> &mut T {
        self.get_mut()
    }
}

impl<'id, T> Default for GhostCell<'id, T>
where
    T: Default,
{
    fn default() -> Self {
        GhostCell::new(T::default())
    }
}
