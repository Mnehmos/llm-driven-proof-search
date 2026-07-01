use std::fs;
use std::path::Path;

#[test]
fn test_core_crate_has_no_provider_sdks() {
    let cargo_toml_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let content = fs::read_to_string(cargo_toml_path).expect("Failed to read Cargo.toml");

    let forbidden_crates = vec![
        "reqwest",
        "async-openai",
        "anthropic",
        "google-genai",
        "genai",
        "hyper",
        "tungstenite",
    ];

    for forbidden in forbidden_crates {
        assert!(
            !content.contains(&format!("{} ", forbidden)) && 
            !content.contains(&format!("{}=", forbidden)) &&
            !content.contains(&format!("{}\n", forbidden)) &&
            !content.contains(&format!("{}\"", forbidden)),
            "chatdb-core must not depend on network or provider SDKs like '{}'",
            forbidden
        );
    }
}
