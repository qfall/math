// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of macros which are used to implement
//! various traits fast without repetition.

pub(crate) mod arithmetics;
pub(crate) mod for_others;
pub(crate) mod from;
pub(crate) mod serialize;
