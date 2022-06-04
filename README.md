# The Joy of State Separating Proofs
Formalisations of proofs from [The Joy of Cryptography](https://joyofcryptography.com/pdf/book.pdf) in [Coq](https://coq.inria.fr/), using [SSProve](https://github.com/SSProve/ssprove).

Namely:
 - [Theorem 3.6](theories/SecretSharing.v) (Simple secret-sharing scheme)
 - [Theorems 3.8, 3.9, and 3.13](theories/ShamirSecretSharing.v) (Shamir's secret-sharing scheme)
 - [Claim 5.5](theories/StretchPRG.v) (Extending the Stretch of a PRG)
 - [Claim 5.10](theories/SymmRatchet.v) (Symmetric Ratchet)
 - [Claim 6.3](theories/PRFPRG.v) (Constructing a PRG from a PRF)
 - [Claim 9.4](theories/PRPCCA.v) (CCA-secure encryption from a strong PRP)
 - [Claim 10.4](theories/PRFMAC.v) (A PRF is a MAC)
 - [Claim 10.10](theories/MACCCA.v) (CCA-security from a MAC scheme)
