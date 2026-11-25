//! Payload boundaries returned by the installed run-command-v1 producer.
use vstd::prelude::*;

verus! {
pub fn split<'a>(bytes: &'a [u8], stdout: usize, stderr: usize, limit: usize)
    -> (parts: Option<(&'a [u8], &'a [u8])>)
    ensures
        parts.is_some() == (stdout <= limit && stderr <= limit
            && stdout as int + stderr as int == bytes@.len()),
        match parts {
            Some((out, err)) => out@ == bytes@.subrange(0, stdout as int)
                && err@ == bytes@.subrange(stdout as int, bytes@.len() as int),
            None => true,
        },
{
    if stdout > limit || stderr > limit || stdout > bytes.len() || bytes.len() - stdout != stderr {
        return None;
    }
    Some(bytes.split_at(stdout))
}
}
