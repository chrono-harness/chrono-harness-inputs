//! Registration proposes installed paths. Capture admits them against its fixed documents.
use std::collections::btree_map::Iter;
use vstd::prelude::*;

verus! {
pub fn same_endpoint(config_matches: bool, selection_matches: bool) -> (accepted: bool)
    ensures accepted == (config_matches && selection_matches),
{
    config_matches && selection_matches
}

pub open spec fn single_member(name: Seq<u8>) -> bool {
    name.len() > 0
        && !(name.len() == 1 && name[0] == 46)
        && !(name.len() == 2 && name[0] == 46 && name[1] == 46)
        && forall|i: int| 0 <= i < name.len() ==> name[i] != 47
}

pub fn permitted(required: bool, absolute: bool, present: bool, member: Option<&[u8]>,
    digest: bool, registered: bool) -> (accepted: bool)
    ensures accepted == (required && absolute && present && digest && registered
        && (member matches Some(name) && single_member(name@))),
{
    if !required || !absolute || !present || !digest || !registered { return false; }
    let Some(name) = member else { return false; };
    if name.is_empty() || (name.len() == 1 && name[0] == 46u8)
        || (name.len() == 2 && name[0] == 46u8 && name[1] == 46u8) { return false; }
    let mut i = 0;
    while i < name.len()
        invariant member == Some(name), required && absolute && present && digest && registered,
            name.len() > 0, !(name.len() == 1 && name@[0] == 46),
            !(name.len() == 2 && name@[0] == 46 && name@[1] == 46),
            i <= name.len(), forall|j: int| 0 <= j < i ==> name@[j] != 47,
        decreases name.len() - i,
    {
        if name[i] == 47u8 { assert(!single_member(name@)); return false; }
        i += 1;
    }
    true
}

/// Use the original BTreeMap iterator and stop before observing any later mapping.
pub fn first_invalid<'a, K: 'a, V: 'a, F: Fn(&K, &V) -> bool>(
    mappings: Iter<'a,K,V>, accept: F,
) -> (bad: Option<&'a K>)
    requires 0 <= mappings@.0 <= mappings@.1.len(),
        forall|key: &K, value: &V| accept.requires((key,value)),
    ensures match bad {
        Some(key) => exists|i: int| mappings@.0 <= i < mappings@.1.len()
            && mappings@.1[i].0 == *key
            && #[trigger] accept.ensures((&mappings@.1[i].0, &mappings@.1[i].1), false)
            && forall|j: int| mappings@.0 <= j < i ==>
                #[trigger] accept.ensures((&mappings@.1[j].0, &mappings@.1[j].1), true),
        None => forall|i: int| mappings@.0 <= i < mappings@.1.len() ==>
            #[trigger] accept.ensures((&mappings@.1[i].0, &mappings@.1[i].1), true),
    },
{
    let mut iter = mappings;
    let ghost initial = mappings@;
    loop
        invariant initial == mappings@, 0 <= initial.0 <= initial.1.len(),
            forall|key: &K, value: &V| accept.requires((key,value)),
            iter@.1 == initial.1, initial.0 <= iter@.0 <= initial.1.len(),
            forall|i: int| initial.0 <= i < iter@.0 ==>
                #[trigger] accept.ensures((&initial.1[i].0, &initial.1[i].1), true),
        decreases initial.1.len() - iter@.0,
    {
        let ghost i = iter@.0;
        let Some((key, value)) = iter.next() else { return None; };
        if !accept(key,value) {
            assert(accept.ensures((&initial.1[i].0, &initial.1[i].1), false));
            return Some(key);
        }
    }
}
}
