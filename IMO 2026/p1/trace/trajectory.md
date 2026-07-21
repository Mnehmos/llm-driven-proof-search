# Proof-search trajectories — IMO 2026 Problem 1

Hash-chain index generated from trajectory_export on 2026-07-16. Full raw event
payloads, including failed proof bodies, remain in the local proof-search
ledger and can be regenerated with trajectory_export using the episode ID.

| Target | Episode | Events | First event hash | Last event hash |
|---|---|---:|---|---|
| Exponent Euclidean-step gcd | e118ad1a-aa66-41c6-819b-6e9e9f1d6c26 | 3 | f78255d17dcef324b93452d8524881b41d329684a90a2dee12b97f7c79971d9f | 78bc659ffe62f30ce8339dbed8a6b876a7b868b031504d0d711a4386631da6f0 |
| Pair product | 8a051323-a560-4c48-963d-6be3eb9f377d | 3 | 1f035e2aefba1a0818696abeffc336a7d89a6d440dd72bda1e0b636d79b1d5a2 | a9a0a62e89a1af9c98108d7aec94b7fe3ba9bd9ab2f21dc731d43b7b392ce96a |
| Bounded lex measure | 0a2f5935-2f6c-4e28-ba07-91781fc7a61a | 3 | 18d93010ffa4da1f5caeeb20f2a7fbdee7546fa8c9fbd1a80f6a6ab5d3381cf5 | bc3c09a709048bb745558c3109b5328941d18a05d846e4ca47a6adf451e27dad |
| Move factorization | 8201d251-26b9-42a7-9205-2a1fc616fc7b | 3 | 4b806ad5d33ad9f05ef505d92f391d3960e057325342fbe645e31889be96f5d4 | 11bb53b1855270b63883e371e7ef3fb80e209d23a5657ae7a0d273f7626f7ea0 |
| Multiset exponent gcd | d0f44790-23cd-4ba4-bb2f-419a208557a8 | 5 | 6c86a4a2d89a8fea9e29def9d5cf31b4b7ea773ed8955bba871f64749d4a1795 | 33c697a35c3b75e597452e98d77712a78bad4a7e2d9b7a30eaeda223bbeef15f |
| Move-local lex decrease | 7ccdfda4-1c74-47e2-987f-6f57d184e03a | 4 | 49f78b609efaa894d258186d27758234bafddac8ca7eb5ed983c8213211fb1a9 | b8a7c3111a654e5769084a7f7d9bab92b03bf1b2817ed9a70e6718dac20cbb36 |
| Termination | 41680cd0-83ce-4c0f-807d-c12457abcc83 | 10 | 3c486482f35626d4966f2f7eac9374afbaff2d1b7dd4180708501aa519f332b5 | 4c46bea39b431efa984d0b1c9f1db76ec4f78a8976f531b547a80fb472a28c36 |
| Complete root | afae1dbb-fca6-4de1-b64d-a74bb53f16b3 | 8 | aa89a5c3a992a56bf70b8fe1d1130b5aed8ef1740926657300085e476cd15acc | 37a4d4e74a60f398fe9d1eab2f80acfa58e2f8ceae1c38a9469edff53ee510d7 |

Each last event is episode_terminated with outcome=kernel_verified and
termination_reason=root_proved. Published proof bodies are in
[../proof/](../proof/); unsuccessful attempts remain in the ledger.
