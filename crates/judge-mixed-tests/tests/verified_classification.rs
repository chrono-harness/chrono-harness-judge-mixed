//! Independent expectations for additions, removals, surface changes and mixed reports.
#![allow(unexpected_cfgs)]
#[path = "../../judge-mixed/src/verified_classification.rs"]
mod policy;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {

fn expect(value: bool) requires value {
    if !value { panic!(); }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn surface_changes_preserve_both_endpoints_and_only_named_semantics() {
    proof {
        reveal_strlit("judge-policy"); reveal_strlit("judge-implementation");
        reveal_strlit("test"); reveal_strlit("product"); reveal_strlit("documentation");
        assert("judge-implementation"@.len() != "product"@.len());
        assert("judge-implementation"@.len() != "test"@.len());
        assert("product"@.len() != "judge-policy"@.len());
        assert("documentation"@.len() != "product"@.len());
        assert("documentation"@.len() != "test"@.len());
        assert("documentation"@.len() != "judge-policy"@.len());
        assert("documentation"@.len() != "judge-implementation"@.len());
    }
    let moved = policy::endpoints(Some("judge-policy"), Some("test")).unwrap();
    expect(moved.whole_rule && moved.product && moved.changes_rule(false));
    let deleted = policy::endpoints(Some("judge-implementation"), None).unwrap();
    expect(deleted.whole_rule && !deleted.product);
    let added = policy::endpoints(None, Some("product")).unwrap();
    expect(!added.whole_rule && added.product);
    expect(!added.changes_rule(false) && added.changes_rule(true));
    let docs = policy::endpoints(Some("documentation"), None).unwrap();
    expect(!docs.product && !docs.changes_rule(false) && docs.changes_rule(true));
    expect(policy::endpoints(None, None).is_none());
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn mixed_warning_requires_both_a_rule_and_a_product() {
    expect(!policy::mixed(0,0));
    expect(!policy::mixed(0,3));
    expect(!policy::mixed(2,0));
    expect(policy::mixed(2,3));
}

}
