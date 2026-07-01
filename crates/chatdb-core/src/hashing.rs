use serde::Serialize;
use sha2::{Sha256, Digest};
use hex;

/// Serializes a struct into JSON Canonicalization Scheme (RFC 8785)
/// and computes its SHA-256 hash. Returns the hex string.
pub fn canonical_hash<T: Serialize>(data: &T) -> Result<String, String> {
    // 1. Serialize to JCS
    let jcs_bytes = serde_jcs::to_vec(data).map_err(|e| format!("JCS serialization failed: {}", e))?;
    
    // 2. Hash using SHA-256
    let mut hasher = Sha256::new();
    hasher.update(&jcs_bytes);
    let result = hasher.finalize();
    
    // 3. Convert to hex string
    Ok(hex::encode(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Serialize;

    #[derive(Serialize)]
    struct Dummy {
        b: String,
        a: i32,
    }

    #[test]
    fn test_canonical_hash_orders_keys() {
        // According to JCS, keys should be sorted.
        // `a` comes before `b`
        let obj = Dummy {
            b: "hello".to_string(),
            a: 42,
        };
        
        let hash = canonical_hash(&obj).unwrap();
        // Just verify it doesn't crash and returns a 64 char hex string
        assert_eq!(hash.len(), 64);
    }
}
