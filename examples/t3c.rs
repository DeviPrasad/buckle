/*
    Copyright 2024 M. Devi Prasad

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/
use std::cmp::min;
use std::io;
use std::net::ToSocketAddrs;

use aes_gcm::{aead, AeadInPlace, Aes128Gcm, Key, KeyInit, Nonce};
use aes_gcm::aes::Aes128Dec;
use hkdf::Hkdf;
use hmac::{Hmac, Mac};
use hmac::digest::consts::U32;
use hmac::digest::generic_array::GenericArray;
use rand_core::{OsRng, RngCore};
use sha2::{Digest, Sha256};
use tokio::io::AsyncWriteExt;
use tokio::net::{TcpSocket, TcpStream};
use x25519_dalek::{EphemeralSecret, PublicKey, SharedSecret};

use buckle::init_logger;

use crate::tls3::{AlertDesc, ApplicationDataMsg, ChangeCipherSpecMsg, CipherSuite, ClientHelloHandshake, Extension, HandshakeType, Mutter, RecordContentType, ServerHelloHandshake, ServerHelloMsgReader};

#[allow(dead_code)]
pub mod tls3 {
    pub type ProtoColVersion = u16;
    pub type Random = [u8; 32];

    pub type CipherSuiteCode = (u8, u8);

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum CipherSuite {
        TlsAes128GcmSha256,
        TlsAes256GcmSha384,
        TlsChacha20Poly1305Sha256,
        TlsAes128CcmSha256,
        TlsAes128Ccm8Sha256,
    }

    impl TryFrom<(u8, u8)> for CipherSuite {
        type Error = Mutter;

        fn try_from(value: (u8, u8)) -> Result<Self, Self::Error> {
            match value {
                (0x13, 0x01) => Ok(CipherSuite::TlsAes128GcmSha256),
                (0x13, 0x02) => Ok(CipherSuite::TlsAes256GcmSha384),
                (0x13, 0x03) => Ok(CipherSuite::TlsChacha20Poly1305Sha256),
                (0x13, 0x04) => Ok(CipherSuite::TlsAes128CcmSha256),
                (0x13, 0x05) => Ok(CipherSuite::TlsAes128Ccm8Sha256),
                _ => Err(Mutter::CipherUnsupported)
            }
        }
    }

    impl CipherSuite {
        pub fn code(&self) -> CipherSuiteCode {
            match self {
                CipherSuite::TlsAes128GcmSha256 => (0x13, 0x01),
                CipherSuite::TlsAes256GcmSha384 => (0x13, 0x02),
                CipherSuite::TlsChacha20Poly1305Sha256 => (0x13, 0x03),
                CipherSuite::TlsAes128CcmSha256 => (0x13, 0x04),
                CipherSuite::TlsAes128Ccm8Sha256 => (0x13, 0x05),
            }
        }
    }

    pub const LEGACY_VER_0X0303: u16 = (0x03_u16 << 8) | 0x3;
    pub const REC_SIZE_BYTES_MAX: usize = 1 << 14;

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum RecordContentType {
        Invalid = 0,
        ChangeCipherSpec = 20,
        Alert = 21,
        Handshake = 22,
        ApplicationData = 23,
        _Unused_ = 255
    }

    #[repr(u8)]
    #[derive(Clone, Copy, Debug, Default, PartialEq)]
    pub enum HandshakeType {
        ClientHello = 1,
        ServerHello = 2,
        NewSessionTicket = 4,
        EndOfEarlyData = 5,
        EncryptedExtensions = 8,
        Certificate = 11,
        CertificateRequest = 13,
        CertificateVerify = 15,
        Finished = 20,
        KeyUpdate = 24,
        MessageHash = 254,
        #[default]
        Bad = 255
    }

    impl From<u8> for HandshakeType {
        fn from(val: u8) -> Self {
            match val {
                1 => HandshakeType::ClientHello,
                2 => HandshakeType::ServerHello,
                4 => HandshakeType::NewSessionTicket,
                5 => HandshakeType::EndOfEarlyData,
                8 => HandshakeType::EncryptedExtensions,
                11 => HandshakeType::Certificate,
                13 => HandshakeType::CertificateRequest,
                15 => HandshakeType::CertificateVerify,
                20 => HandshakeType::Finished,
                24 => HandshakeType::KeyUpdate,
                _ => HandshakeType::Bad,
            }
        }
    }

    #[repr(u16)]
    #[derive(Clone, Debug, PartialEq, Copy)]
    pub enum ExtensionTypeCode {
        ServerName = 0,
        MaxFragmentLength = 1,
        StatusRequest = 5,
        SupportedGroups = 10,
        ECPointFormats = 11,
        SignatureAlgorithms = 13,
        UseSrtp = 14,
        Heartbeat = 15,
        ApplicationLayerProtocolNegotiation = 16,
        SignedCertificateTimestamp = 18,
        ClientCertificateType = 19,
        ServerCertificateType = 20,
        Padding = 21,
        EncryptThenMAC = 22,
        ExtendedMasterSecret = 23,
        SessionTicket = 35,
        PreSharedKeys = 41,
        EarlyData = 42,
        SupportedVersions = 43,
        Cookie = 44,
        PskKeyExchangeModes = 45,
        CertificateAuthorities = 47,
        OidFilters = 48,
        PostHandshakeAuth = 49,
        SignatureAlgorithmsCert = 50,
        KeyShare = 51,
        Unused = 65535
    }

    // B.3.1.4. Supported Groups Extension. page 130.
    #[repr(u16)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum SupportedGroup {
        Reserved = 0,
        // elliptic curve groups
        Secp256r1 = 0x0017,
        Secp384r1 = 0x0018,
        Secp512r1 = 0x0019,
        X25519 = 0x001D,
        X448 = 0x001E,
        // finite-field groups
        FFDHE2048 = 0x0100,
        FFDHE3072 = 0x0101,
        FFDHE4096 = 0x0102,
        FFDHE6144 = 0x0103,
        FFDHE8192 = 0x0104,

        Unused = 0xFFFF,
    }

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum AlertDesc {
        CloseNotify = 0,
        UnexpectedMessage = 10,
        BadRecordMac = 20,
        RecordOverflow = 22,
        HandshakeFailure = 40,
        BadCertificate = 42,
        UnsupportedCertificate = 43,
        CertificateRevoked = 44,
        CertificateExpired = 45,
        CertificateUnknown = 46,
        IllegalParameter = 47,
        UnknownCA = 48,
        AccessDenied = 49,
        DecodeError = 50,
        DecryptError = 51,
        ProtocolVersion = 70,
        InsufficientSecurity = 71,
        InternalError = 80,
        UserCanceled = 90,
        MissingExtension = 109,
        UnsupportedExtension = 110,
        UnrecognizedName = 112,
        BadCertificateStatusResponse = 113,
        CertificateRequired = 116,
        Bad = 255,
    }

    impl TryFrom<u8> for AlertDesc {
        type Error = Mutter;

        fn try_from(desc: u8) -> Result<Self, Self::Error> {
            match desc {
                0 => Ok(AlertDesc::CloseNotify),
                22 => Ok(AlertDesc::RecordOverflow),
                40 => Ok(AlertDesc::HandshakeFailure),
                50 => Ok(AlertDesc::DecodeError),
                70 => Ok(AlertDesc::ProtocolVersion),
                71 => Ok(AlertDesc::InsufficientSecurity),
                80 => Ok(AlertDesc::InternalError),
                109 => Ok(AlertDesc::MissingExtension),
                110 => Ok(AlertDesc::UnsupportedExtension),
                _ => Err(Mutter::UnknownAlertDesc),
            }
        }
    }

    pub type KeyShareExtData<'a> = (usize, &'a [u8]);

    #[derive(Clone, Debug)]
    pub enum ExtensionType {
        Ed25519KeyShare([u8; 32]),
        SupportedVersionTls13,
    }

    impl ExtensionTypeCode {
        fn from((u, v): (u8, u8)) -> Result<Self, Mutter> {
            match (u, v) {
                (0, 0) => Ok(Self::ServerName),
                (0, 10) => Ok(Self::SupportedGroups),
                (0, 11) => Ok(Self::ECPointFormats),
                (0, 13) => Ok(Self::SignatureAlgorithms),
                (0, 16) => Ok(Self::ApplicationLayerProtocolNegotiation),
                (0, 17) => Ok(Self::ExtendedMasterSecret),
                (0, 22) => Ok(Self::EncryptThenMAC),
                (0, 23) => Ok(Self::ExtendedMasterSecret),
                (0, 35) => Ok(Self::SessionTicket),
                (0, 43) => Ok(Self::SupportedVersions),
                (0, 45) => Ok(Self::PskKeyExchangeModes),
                (0, 51) => Ok(Self::KeyShare),
                _ => {
                    log::error!("ExtensionType - error. Unsupported type {v}");
                    Err(Mutter::UnsupportedExtension)
                }
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct CipherSuites(Vec<CipherSuite>);

    impl TryFrom<Vec<CipherSuite>> for CipherSuites {
        type Error = Mutter;

        fn try_from(cipher_suites: Vec<CipherSuite>) -> Result<Self, Mutter> {
            if !cipher_suites.is_empty() {
                let mut cipher_suite_dup: Vec<bool> = vec![true, false, false, false, false, false];
                for cs in cipher_suites.iter() {
                    let (_, cl) = cs.code();
                    if cipher_suite_dup[cl as usize] {
                        return Err(Mutter::CipherDuplicate)
                    } else {
                        cipher_suite_dup[cl as usize] = true;
                    }
                }
                Ok(CipherSuites(cipher_suites))
            } else {
                Err(Mutter::CipherSuiteLen)
            }
        }
    }

    impl CipherSuites {
        pub fn deserialize(bytes: &[u8]) -> Result<(CipherSuites, usize), Mutter> {
            let mut i: usize = 0;
            // cipher suites - len followed by identifiers; sequence of byte-pairs.
            let cipher_suite_len: usize = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            if (cipher_suite_len & 1 == 1) || !(2..=10).contains(&cipher_suite_len) {
                return Err(Mutter::CipherSuiteLen)
            }
            i += 2;
            let mut cipher_suites: Vec<CipherSuite> = vec![];
            let mut cipher_suite_dup = [true, false, false, false, false, false];
            for k in (0..cipher_suite_len).step_by(2) {
                let cm = bytes[i + k];
                let cl = bytes[i + 1 + k];
                let cs = CipherSuite::try_from((cm, cl))?;
                log::info!("\tcipher_suite: {cs:#?}");
                if cipher_suite_dup[cl as usize] {
                    return Err(Mutter::CipherDuplicate)
                } else {
                    cipher_suite_dup[cl as usize] = true;
                    cipher_suites.push(cs);
                }
            }
            log::info!("\tdeserialized cipher_suites: {cipher_suites:#?}");
            Ok((CipherSuites(cipher_suites), cipher_suite_len + 2))
        }

        pub fn serialize(&self, bytes: &mut [u8]) -> usize {
            let cs_len = (self.0.len() * 2) as u16;
            let mut i = 0;
            bytes[i..i + 2].copy_from_slice(&cs_len.to_be_bytes());
            i += 2;
            for cs in self.0.iter() {
                (bytes[i], bytes[i + 1]) = cs.code();
                i += 2;
            }
            i
        }

        pub fn count(&self) -> usize {
            self.0.len()
        }
    }

    // TODO: define a trait for extension type. Define concrete implementations.
    #[derive(Clone, Copy, Debug)]
    pub struct Extension<'a> {
        xtc: ExtensionTypeCode,
        data: Option<&'a [u8]>,
    }

    struct Extensions {}

    impl Extensions {
        // 'bytes' holds a list of extensions. The first two bytes encode the size of the list,
        fn deserialize(bytes: &[u8]) -> Result<(Vec<Extension>, usize), Mutter> {
            // extensions - length in two bytes
            let ext_len: usize = ((bytes[0] as usize) << 8) | bytes[1] as usize;
            if ext_len == 0 || ext_len > bytes.len() {
                return Err(Mutter::ExtensionLen)
            }
            let bytes: &[u8] = &bytes[2..];
            let mut i: usize = 0;
            // list of extensions
            let mut extensions: Vec<Extension> = vec![];
            while i < ext_len {
                let (ext, len) = Extension::deserialize(bytes, i)?;
                i += len;
                extensions.push(ext);
                assert!(i <= ext_len);
            }
            assert_eq!(i, ext_len);
            Ok((extensions, ext_len + 2))
        }

        fn size(extensions: &[Extension]) -> usize {
            extensions.iter().fold(0, |acc, ext| acc + ext.size())
        }
    }

    impl<'a> Extension<'a> {
        pub fn server_name(name: &'a str) -> Self {
            Extension {
                xtc: ExtensionTypeCode::ServerName,
                data: Some(name.as_bytes())
            }
        }

        pub fn session_null_ticket() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SessionTicket,
                data: Some(&[0, 35, 0, 0])
            }
        }

        pub fn supported_ver_1_3() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SupportedVersions,
                data: Some(&[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03, 0x04])
            }
        }

        pub fn ed25519_key_share(data: &'a [u8; 32]) -> Self {
            Extension {
                xtc: ExtensionTypeCode::KeyShare,
                data: Some(data.as_slice())
            }
        }

        pub fn supported_group_x25519() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SupportedGroups,
                data: None,
            }
        }

        pub fn signature_algorithm_ed25519() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SignatureAlgorithms,
                data: None,
            }
        }

        fn key_share(&self) -> bool {
            self.xtc == ExtensionTypeCode::KeyShare
        }

        fn verify(&self) -> Result<&Self, Mutter> {
            if self.xtc == ExtensionTypeCode::SupportedVersions && self.data != Some(&[0x03_u8, 0x04]) {
                Err(Mutter::UnsupportedVersion)
            } else {
                Ok(self)
            }
        }
        fn size(&self) -> usize {
            match self.xtc {
                ExtensionTypeCode::SupportedVersions => 7,
                // ed25519 key is 32 bytes + 10 bytes prefix describing the key share
                ExtensionTypeCode::KeyShare => 42,
                ExtensionTypeCode::SupportedGroups => 10 /* TODO: include secp256r1 key share */,
                ExtensionTypeCode::SignatureAlgorithms => 12, // 14,
                ExtensionTypeCode::ServerName => {
                    let sn = self.data.expect("server name is mandatory for TLS 1.3");
                    sn.len() + 9
                },
                ExtensionTypeCode::SessionTicket => 4,
                _ => {
                    panic!("Extension.size for unknown type!!");
                },
            }
        }

        fn deserialize(bytes: &'a [u8], start: usize) -> Result<(Extension<'a>, usize), Mutter> {
            let mut i = start;
            let xtc = (bytes[i], bytes[i + 1]);
            let ext_type_code = ExtensionTypeCode::from(xtc)?;
            i += 2;
            let xt_data_len: usize;
            (xt_data_len, i) = if ext_type_code == ExtensionTypeCode::SupportedVersions {
                if bytes[i] == 0 {
                    (bytes[i + 1] as usize, i + 2)
                } else {
                    (bytes[i] as usize, i)
                }
            } else if ext_type_code == ExtensionTypeCode::KeyShare {
                let curve_id = ((bytes[i + 2] as u16) << 8) | (bytes[i + 3] as u16);
                let key_share_ext_len = ((bytes[i] as usize) << 8) | (bytes[i + 1] as usize);
                log::info!("extension {:?} ext_total_len = {}, curve = {}", ext_type_code, key_share_ext_len, curve_id);

                if curve_id == SupportedGroup::Secp256r1 as u16 {
                    log::error!("Error - Support for secp256r1 key share is not yet available");
                    return Err(Mutter::Secp256r1NotYetSupported)
                }
                let x25519_key_len = ((bytes[i + 4] as usize) << 8) | (bytes[i + 5] as usize);
                if x25519_key_len != 32 {
                    return Err(Mutter::X25519KeyLenBad)
                }
                (x25519_key_len, i + 6)
            } else {
                (0, i)
            };
            if xt_data_len > 0 {
                log::info!("extension {:?} xt_data_len = {}", ext_type_code, xt_data_len);
                let k = i + xt_data_len;
                let ext: Extension = *Extension {
                    xtc: ext_type_code,
                    data: Some(bytes[i..k].iter().as_slice()),
                }.verify()?;

                Ok((ext, k - start))
            } else {
                Err(Mutter::UnsupportedExtension)
            }
        }

        pub fn serialize(&self, bytes: &'a mut [u8], i: usize) -> usize {
            match self.xtc {
                ExtensionTypeCode::ServerName => {
                    let sn = self.data.expect("server name is mandatory for TLS 1.3");
                    let snl = sn.len() as u8;
                    bytes[i..i + 9 + snl as usize].copy_from_slice(
                        &[[0, 0, 0, snl + 5, 0, snl + 3, 0, 0, snl].as_slice(), sn].concat());
                    (9 + snl) as usize
                },

                ExtensionTypeCode::SessionTicket => {
                    let st = self.data.expect("session ticket missing.");
                    bytes[i..i + 4].copy_from_slice(st);
                    st.len()
                },

                ExtensionTypeCode::SupportedVersions => {
                    bytes[i..i + 7].copy_from_slice(&[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03, 0x04]);
                    7
                },

                ExtensionTypeCode::KeyShare => {
                    if let Some(key) = self.data {
                        let len = key.len() as u8;
                        bytes[i..i + 10].copy_from_slice(&[
                            0, 51, // extension "Key Share"
                            0, len + 6, // 38 bytes of "Key Share" extension data follows
                            0, len + 4, // 36 bytes of key share data follows
                            0, 29, // value for x25519 (key exchange via curve25519)
                            0, len, // 32 bytes of public key follows
                        ]);
                        bytes[i + 10..i + 10 + len as usize].copy_from_slice(key);
                        len as usize + 10
                    } else {
                        0
                    }
                },

                ExtensionTypeCode::SupportedGroups => {
                    let n = 10u8;
                    bytes[i..i + n as usize].copy_from_slice(&[
                        0, 0x0a, // extension "Supported Groups"
                        0, n - 4, // 4 bytes of "Supported Groups" extension data follows
                        0, n - 6, // 2 bytes of the curve data follows
                        0, 0x1d, // value for the curve x25519
                        0, 0x17, // value for the curve secp256r1
                    ]);
                    n as usize
                },

                // page 102, section 9.1, Mandatory-to-implement cipher suites.
                // 'mozilla.org', 'yourdot.net', 'usa.gov' require the following two algorithms.
                // MUST support RSA-PSS-RSAE-SHA256 for CertificateVerify and certificates.
                // MUSt support ECDSA-SECP256r1-SHA256.
                // MUST support RSA-PKCS1-SHA256 for certificates.
                ExtensionTypeCode::SignatureAlgorithms => {
                    let n = 12u8;
                    bytes[i..i + n as usize].copy_from_slice(&[
                        0, 0x0d, // extension "Signature Algorithms""
                        0, n - 4, // 4 bytes of "Signature Algorithms" extension data follows
                        0, n - 6, // 2 bytes of the algorithm identifier
                        8, 7, // value for the ED25519
                        4, 3, // value for the ECDSA-SECP256r1-SHA256 - P256
                        8, 4, // value for RSA-PSS-RSAE-SHA256
                        // 4, 1, // RSA_PKCS1_SHA256
                    ]);
                    n as usize
                }
                _ => 0
            }
        }
    }

    struct CompressionMethods {}

    impl CompressionMethods {
        pub fn deserialize(bytes: &[u8]) -> Result<usize, Mutter> {
            // compression methods
            if !(bytes[0] == 1 && bytes[1] == 0) {
                return Err(Mutter::CompressionMethods)
            }
            Ok(2)
        }
    }

    #[derive(Clone, Debug)]
    pub struct ClientHelloHandshake<'a> {
        // TLSPlainText; page 79, sec 5.1. Record Layer
        rct: RecordContentType, // record content type - Handshake(22)
        // TLS 1.3 has deprecated the legacy record version indicator.
        // It MUST be set to 0x0303, and ignored for all practical purposes.
        legacy_rec_ver: ProtoColVersion, // lvalue: u16 = 0x0303
        fragment_len: u16,
        // Handshake; Page 25, sec 4. Handshake Protocol
        ht: HandshakeType, // handshake type is ClientHello(1)
        len: u32,
        // ClientHello, page 28, sec 4.1.2. Client Hello
        legacy_tls_ver: ProtoColVersion, // value: u16 == 0x0303
        random: Random,
        legacy_session_id: Option<&'a [u8]>, // if [1, 0]
        // B.4. Cipher Suites. Use AES and/or CHACHA20,.
        // TlsAes128GcmSha256 (0x13, 0x01)
        // TlsAes256GcmSha384 (0x13, 0x02)
        // TLS_CHACHA20_POLY1305_SHA256 (0x13, 0x03)
        cipher_suites: CipherSuites,
        // size 1 to 255.
        legacy_compression_methods: [u8; 2], // value == [1, 0]
        extensions: Vec<Extension<'a>>,
    }

    #[allow(dead_code)]
    impl<'a> ClientHelloHandshake<'a> {
        pub fn try_from(random: Random, ciphers: Vec<CipherSuite>, extensions: Vec<Extension<'a>>) -> Result<Self, Mutter> {
            let ch_data_len =
                48 +
                    ciphers.len() * 2 +
                    4 +
                    Extensions::size(&extensions);

            if ch_data_len >= (1 << 14) + 3 {
                return Err(Mutter::TooBig);
            }

            Ok(ClientHelloHandshake {
                rct: RecordContentType::Handshake,
                legacy_rec_ver: LEGACY_VER_0X0303,
                fragment_len: (ch_data_len - 3) as u16,
                ht: HandshakeType::ClientHello,
                len: (ch_data_len - 9) as u32,
                legacy_tls_ver: LEGACY_VER_0X0303,
                random,
                legacy_session_id: Some(&[2, 1, 0]),
                cipher_suites: CipherSuites::try_from(ciphers)?,
                legacy_compression_methods: [1, 0], // no legacy compression methods in TLS 1.3
                extensions,
            })
        }

        fn size(&self) -> usize {
            1 + // 0: content_type
                2 + // 1: legacy_rec_version
                2 + // 3: fragment_len
                1 + // 5: handshake_type = client_hello == 1
                3 + // 6: message_len = (fragment_len - 4)
                2 + // 9: legacy_version
                32 + // 11: random
                1 + // 43: session_id_len = 0. In our implementation, value == 0
                2 + // 44: cipher_suite_len; uses 2 bytes (u16)
                // 46: list_of(cipher_suite) -- cipher_suite_len bytes
                2 * self.cipher_suites.count() +
                2 + // (46 + cipher_suite_len): compression_methods = (1, 0)
                2 + // (46 + cipher_suite_len + 2): ext_len
                // (46 + cipher_suite_len + 2 + 2): list_of(extension)
                self.extensions.iter().fold(0, |acc, ext| acc + ext.size())
        }

        pub fn serialize(&self, bytes: &'a mut [u8]) -> Result<usize, Mutter> {
            // first five bytes of the message hold content_type, legacy_version, and fragment_len.
            let frag_len: u16 = self.size() as u16 - 5;
            bytes[0..3].copy_from_slice(&[
                22, // 0: content_type = handshake
                0x3, 0x03 // 1: legacy_record_version
            ]);
            // 3: fragment_len
            bytes[3..5].copy_from_slice(&frag_len.to_be_bytes());
            let mut i: usize = 5;
            // 5: handshake_type; client_hello == 1
            bytes[i] = 1;
            i += 1;
            // 6: message_len - 3 bytes.
            bytes[i] = 0;
            bytes[i + 1..i + 3].copy_from_slice(&(frag_len - 4).to_be_bytes());
            i += 3;
            // 9: legacy_version
            (bytes[i], bytes[i + 1]) = (3, 3);
            i += 2;
            // 11: random
            //for x in 0..32_u8 {
            //    bytes[i + x as usize] = x + 100;
            //}
            bytes[i..i + 32].copy_from_slice(self.random.as_slice());
            i += 32;
            // 43: session_id = (0) - essentially an empty session id.
            bytes[i] = 0;
            i += 1;
            // 46: (0, cipher_suite_len, ...)
            i += self.cipher_suites.serialize(&mut bytes[i..]);
            // 50: compression_methods = (1, 0)
            (bytes[i], bytes[i + 1]) = (1, 0);
            // 51: extensions_len (2 bytes)
            i += 2;
            let k = i;
            i += 2;
            // 53: extensions
            for ext in self.extensions.iter() {
                i += ext.serialize(bytes, i);
            }
            (bytes[k], bytes[k + 1]) = (0, (i - k - 2) as u8);
            Ok(i)
        }

        pub fn deserialize(bytes: &'a [u8]) -> Result<ClientHelloHandshake<'a>, Mutter> {
            let mut i: usize = 0;
            if bytes[i] != RecordContentType::Handshake as u8 {
                return Err(Mutter::RecType)
            }
            i += 1; // 1
            if (((bytes[i] as u16) << 8) | bytes[i + 1] as u16) != LEGACY_VER_0X0303 {
                return Err(Mutter::LegacyRecordVer)
            }
            i += 2; // 3
            let frag_len: usize = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            if !(64..=REC_SIZE_BYTES_MAX).contains(&frag_len) {
                return Err(Mutter::FragmentLen)
            }
            i += 2; // 5
            assert_eq!(bytes.len() - 5, frag_len);
            log::info!("frag_len = {frag_len}");
            if bytes[i] != HandshakeType::ClientHello as u8 {
                return Err(Mutter::HandshakeType)
            }
            i += 1; // 6
            let msg_len: usize = ((bytes[i] as usize) << 16) | ((bytes[i + 1] as usize) << 8) | (bytes[i + 2] as usize);
            if !(64..=REC_SIZE_BYTES_MAX).contains(&msg_len) {
                return Err(Mutter::MsgLen)
            }
            assert_eq!(frag_len - 4, msg_len);
            i += 3; // 9
            log::info!("msg_len = {msg_len}");
            if (((bytes[i] as u16) << 8) | bytes[i + 1] as u16) != LEGACY_VER_0X0303 {
                return Err(Mutter::LegacyTLS13MsgVer)
            }
            i += 2; // 11
            let _random: &[u8] = &bytes[i..i + 32];
            i += 32; // 43
            let sid_len: u8 = bytes[i];
            log::info!("session_id_len = {sid_len}");
            if sid_len > 32 {
                return Err(Mutter::SessionIdLen)
            }
            // copy session_id including its length
            let _sid =
                if sid_len > 0 {
                    Some(&bytes[i..(i + sid_len as usize)])
                } else {
                    None
                };
            i += (sid_len + 1) as usize;

            // cipher suites - len followed by identifiers; sequence of byte-pairs.
            let (_cipher_suites, cipher_suite_len) = CipherSuites::deserialize(&bytes[i..])?;
            i += cipher_suite_len;

            i += CompressionMethods::deserialize(&bytes[i..i + 2])?;

            let (_extensions, ext_len) = Extensions::deserialize(&bytes[i..])?;
            i += ext_len;

            assert_eq!(i, frag_len + 5);
            Err(Mutter::BadInput)
        }
    }

    #[derive(Debug)]
    pub struct ServerHelloHandshake<'a> {
        // TLSPlainText; page 79, sec 5.1. Record Layer
        rct: RecordContentType, // record content type - Handshake(22)
        // TLS 1.3 has deprecated the legacy record version indicator.
        // It MUST be set to 0x0303, and ignored for all practical purposes.
        legacy_rec_ver: ProtoColVersion, // legacy record version; value: u16 = 0x0303
        pub(crate) fragment_len: u16,
        // Handshake; Page 25, sec 4. Handshake Protocol
        ht: HandshakeType, // handshake type is ServerHello(2)
        pub(crate) len: u32,
        // ServerHello, page 31, sec 4.1.3. Server Hello
        legacy_tls_ver: ProtoColVersion, // value: u16 == 0x0303
        pub(crate) random: Random,
        // Echo of the contents of 'legacy_session_id' field from client's ClientHello message.
        pub(crate) legacy_session_id: Option<&'a [u8]>,
        // B.4. Cipher Suites. Dance with either AES or CHACHA20!
        // TlsAes128GcmSha256 (0x13, 0x01)
        // TlsAes256GcmSha384 (0x13, 0x02)
        // TLS_CHACHA20_POLY1305_SHA256 (0x13, 0x03)
        pub(crate) cipher_suite: CipherSuite,
        // TLS 1.3 client MUST send a vector [1, 0] for compression methods.
        // The TLS 1.3 server MUST echo the same value.
        legacy_compression_method: u8, // value == 0
        // ServerHello, page 32, sec 4.1.3. Server Hello
        // TLS 1.3 MUST contain the "supported_versions" extension.
        // It may contain either "pre_shared_key" or the "key_share" extension, or both.
        pub(crate) extensions: Vec<Extension<'a>>,
    }

    #[allow(dead_code)]
    impl<'a> ServerHelloHandshake<'a> {
        pub fn new(rec_frag_len: u16, random: Random, sid: Option<&'a [u8]>, cipher: CipherSuite, extensions: Vec<Extension<'a>>) -> Self {
            ServerHelloHandshake {
                rct: RecordContentType::Handshake,
                legacy_rec_ver: LEGACY_VER_0X0303,
                fragment_len: rec_frag_len,
                ht: HandshakeType::ServerHello,
                len: (rec_frag_len - 4) as u32,
                legacy_tls_ver: LEGACY_VER_0X0303,
                random,
                legacy_session_id: sid,
                cipher_suite: cipher,
                legacy_compression_method: 0,
                extensions,
            }
        }

        pub fn deserialize(reader: &'a mut ServerHelloMsgReader) -> Result<(ServerHelloHandshake<'a>, usize), Mutter> {
            reader.read()
        }

        // TODO: extensions must type check using traits
        pub fn x25519_key(&self) -> Result<[u8; 32], Mutter> {
            if let Some(&xt) = self.extensions
                                   .iter().find(|ext| ext.xtc == ExtensionTypeCode::KeyShare) {
                if let Some(bytes) = xt.data {
                    return bytes.try_into()
                                .map_err(|_| Mutter::X25519KeyLenBad)
                }
            }
            Err(Mutter::MissingX25519Key)
        }
    }

    #[derive(Clone, Debug)]
    pub struct ServerHelloMsgReader<'a> {
        i: usize,
        bytes: &'a [u8],
    }

    #[allow(dead_code)]
    impl<'a> ServerHelloMsgReader<'a> {
        pub fn new(bytes: &'a [u8]) -> Self {
            Self {
                i: 0,
                bytes,
            }
        }

        pub fn pos(&self) -> usize {
            self.i
        }

        fn slide(&mut self, c: usize) {
            if c == 0 {
                log::error!("slide: zero size!!");
            }
            debug_assert!(self.i + c <= self.bytes.len(), "ServerHelloMsgReader.slide");
            self.i += c;
        }

        fn peek_u8(&self) -> u8 {
            self.bytes[self.i]
        }

        fn peek_u16(&self) -> u16 {
            ((self.bytes[self.i] as u16) << 8) | (self.bytes[self.i + 1] as u16)
        }

        fn peek_u24(&self) -> usize {
            ((self.bytes[self.i] as usize) << 16) | ((self.bytes[self.i + 1] as usize) << 8) | (self.bytes[self.i + 2] as usize)
        }

        fn read_u8(&mut self) -> u8 {
            (self.peek_u8(), self.slide(1)).0
        }

        fn read_u16(&mut self) -> u16 {
            (self.peek_u16(), self.slide(2)).0
        }

        fn read_u24(&mut self) -> usize {
            (self.peek_u24(), self.slide(3)).0
        }

        fn u8(&mut self, val: u8) -> bool {
            (self.bytes[self.i] == val, self.slide(1)).0
        }

        fn u16(&mut self, val: u16) -> bool {
            (self.peek_u16() == val, self.slide(2)).0
        }

        fn read_bytes(&mut self, n: usize) -> &'a [u8] {
            (&self.bytes[self.i..self.i + n], self.slide(n)).0
        }

        fn read_extensions(&mut self) -> Result<Vec<Extension<'a>>, Mutter> {
            // eprintln!("read_extensions i = {}, {:?}", self.i, &self.bytes[self.i..]);
            let (extensions, ext_len) = Extensions::deserialize(&self.bytes[self.i..])?;
            self.slide(ext_len);
            Ok(extensions)
        }

        fn read_empty_compression_methods(&mut self) -> Result<bool, Mutter> {
            if self.read_u8() == 0 {
                Ok(true)
            } else {
                Err(Mutter::CompressionMethods)
            }
        }

        fn read_random(&mut self) -> Result<Random, Mutter> {
            self.read_bytes(32).try_into().map_err(|_| Mutter::RandomVal)
        }

        fn read_session_id(&mut self) -> Option<&'a [u8]> {
            let sid_len: usize = self.read_u8() as usize;
            // log::info!("read_session_id: len = {sid_len}");
            if sid_len > 0 {
                let sid: &[u8] = self.read_bytes(sid_len);
                Some(sid)
            } else {
                None
            }
        }

        pub fn read(&mut self) -> Result<(ServerHelloHandshake<'a>, usize), Mutter> {
            if !self.u8(RecordContentType::Handshake as u8) {
                return Err(Mutter::RecType)
            }
            if !self.u16(LEGACY_VER_0X0303) {
                return Err(Mutter::LegacyRecordVer)
            }
            let frag_len: usize = self.read_u16() as usize;
            assert_eq!(self.pos(), 5);
            if !(32..=REC_SIZE_BYTES_MAX).contains(&frag_len) {
                return Err(Mutter::FragmentLen)
            }
            if !self.u8(HandshakeType::ServerHello as u8) {
                return Err(Mutter::HandshakeType)
            }
            let msg_len: usize = self.read_u24();
            if !(32..=REC_SIZE_BYTES_MAX).contains(&msg_len) {
                return Err(Mutter::MsgLen)
            }
            assert_eq!(frag_len - 4, msg_len);
            if !self.u16(LEGACY_VER_0X0303) {
                return Err(Mutter::LegacyTLS13MsgVer)
            }
            let random: Random = self.read_random()?;
            let sid = self.read_session_id();
            let cipher_suite = CipherSuite::try_from((self.read_u8(), self.read_u8()))?;
            self.read_empty_compression_methods()?;

            let extensions = self.read_extensions()?;

            Ok((ServerHelloHandshake::new((frag_len & 0xFFFF) as u16,
                                          random,
                                          sid,
                                          cipher_suite,
                                          extensions), self.i))
        }
    }

    pub struct ChangeCipherSpecMsg(());

    impl ChangeCipherSpecMsg {
        pub fn deserialize(bytes: &[u8]) -> Result<(Option<Self>, usize), Mutter> {
            if bytes[0] != RecordContentType::ChangeCipherSpec as u8 {
                return Ok((None, 0))
            }
            if bytes.len() < 6 {
                return Err(Mutter::BadInput)
            }
            if (bytes[1], bytes[2]) != (0x3, 0x3) {
                return Err(Mutter::UnsupportedVersion)
            }
            if (bytes[3], bytes[4], bytes[5]) != (0x0, 0x1, 0x1) {
                return Err(Mutter::InvalidCipherSpecChange)
            }
            log::info!("ChangeCipherSpecMsg - Ok");
            Ok((Some(ChangeCipherSpecMsg(())), 6))
        }
    }

    pub struct ApplicationDataMsg {}

    impl ApplicationDataMsg {
        pub fn deserialize(bytes: &[u8]) -> Result<usize, Mutter> {
            if bytes.is_empty() || bytes.len() < 6 {
                Err(Mutter::BadInput)
            } else if bytes[0] != RecordContentType::ApplicationData as u8 {
                log::info!("ApplicationDataMsg::deserialize - nothing to do.");
                Ok(0)
            } else if (bytes[1], bytes[2]) != (0x3, 0x3) {
                Err(Mutter::UnsupportedVersion)
            } else {
                // log::info!("ApplicationDataMsg prefix_slice = {:?}", &bytes[0..8]);
                let data_len = ((bytes[3] as usize) << 8) | (bytes[4] as usize);
                // log::info!("application data len = {data_len}/{}, data(pre8): {:?}, data(last8): {:?}", bytes.len(),  &bytes[0..8], &bytes[data_len+5-8..data_len+10]);
                Ok(5 + data_len)
            }
        }
    }

    #[repr(u8)]
    #[derive(Clone, Debug)]
    pub enum Mutter {
        RecType = 1,
        LegacyRecordVer = 2,
        FragmentLen = 4,
        LegacyTLS13MsgVer = 7,
        MsgLen = 10,
        RandomVal = 14,
        SessionIdLen = 19,
        CipherSuiteLen = 23,
        CipherUnsupported = 28,
        CipherDuplicate = 31,
        CipherBad = 37,
        CompressionMethods = 41,
        ExtensionLen = 44,
        ExtensionType = 47,
        UnsupportedExtension = 48,
        UnsupportedVersion = 50,
        UnsupportedHandshakeMessageType = 53,
        ExtensionData = 59,

        HandshakeType = 129,
        UnknownAlertDesc = 140,
        InvalidCipherSpecChange = 145,

        BadNetworkAddress = 165,
        TlsConnection = 166,
        TlsChannelReadiness = 167,
        StreamError = 168,
        SocketPropertyError = 171,

        TooBig = 221,
        MsgSizeInvalid = 222,
        NotImpl = 224,

        RandomGen = 238,
        MissingX25519Key = 240,
        Secp256r1NotYetSupported = 244,
        X25519KeyLenBad = 247,

        BadInput = 255,
    }
}

// TODO: clear the values after use
pub struct X25519KeyPair(EphemeralSecret, PublicKey);
impl Default for X25519KeyPair {
    fn default() -> Self {
        let sk = EphemeralSecret::random();
        let pk = PublicKey::from(&sk);
        Self(sk, pk)
    }
}

impl X25519KeyPair {
    pub fn public_bytes(&self) -> &[u8; 32] {
        self.1.as_bytes()
    }

    pub fn dh(self, peer_pk_bytes: [u8; 32]) -> SharedSecret {
        let peer_pk = PublicKey::from(peer_pk_bytes);
        self.0.diffie_hellman(&peer_pk)
    }
}

pub struct CryptoRandom<const N: usize> ();

impl<const N: usize> CryptoRandom<N> {
    pub fn bytes() -> Result<[u8; N], Mutter> {
        let mut buf = [0u8; N];
        OsRng.fill_bytes(&mut buf);
        Ok(buf)
    }
}

// section 7.1, Key Schedule. pages 92-94.
// page 93 displays the sequence of steps in deriving different secrets.
pub struct KeySchedule<const HASH_LEN: usize> {
    //psk: [u8; LEN],
    //dhe_secret: [u8; LEN],
}

// WARNING - hardcoded hash function!
// TODO - figure out how HKDF selection works.
#[allow(dead_code)]
impl<const HASH_LEN: usize> KeySchedule<HASH_LEN> {
    fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let (prk, _hk) = Hkdf::<Sha256>::extract(Some(salt), ikm);
        assert_eq!(prk.len(), HASH_LEN);
        assert_ne!(prk.as_slice(), [0; HASH_LEN]);
        prk.to_vec()
    }

    // 'secret' is the pseudo-random key (prk)
    fn hkdf_expand_label(secret: &[u8], label: &str, ctx: &[u8], output_len: u16) -> Vec<u8> {
        // log::info!("hkdf_expand_label - label:{label:}, ctx:{ctx:?}, secret:{secret:?}");
        assert_eq!(secret.len(), HASH_LEN);
        assert!(!label.is_empty() && label.len() <= 255);
        let label_len = ("tls13 ".len() + label.len()) as u16;
        assert!(label_len > 6 && label_len <= 255);
        let ctx_len = ctx.len() as u16;
        assert!(ctx.len() <= 255);
        let hkdf_label_full_len = 4 + label_len + ctx_len;
        assert!(hkdf_label_full_len <= 514);

        let mut hkdf_label: Vec<u8> = Vec::new(); //vec![0; hkdf_label_full_len as usize];
        let hash_len_bytes = output_len.to_be_bytes();
        hkdf_label.push(hash_len_bytes[0]); // 0
        hkdf_label.push(hash_len_bytes[1]); // 1
        // log::info!("hkdf_expand_label - label_len:{label_len:},\n\tctx_len:{ctx_len:},\n\thkdf_label_full_len:{hkdf_label_full_len:}\n\thash_len_bytes:{hash_len_bytes:?}");

        hkdf_label.push(label_len as u8); // 2
        hkdf_label.append(&mut ["tls13 ".as_bytes(), label.as_bytes()].concat()); // 3..3+label_len

        hkdf_label.push(ctx_len as u8); // 3+label_len
        if ctx_len > 0 {
            hkdf_label.resize(hkdf_label_full_len as usize, 0);
            hkdf_label[4 + label_len as usize..hkdf_label_full_len as usize].copy_from_slice(ctx)
        }
        let hk = Hkdf::<Sha256>::from_prk(secret).expect("random secret value to be large enough");
        let mut okm = vec![0u8; output_len as usize];
        hk.expand(&hkdf_label, &mut okm).expect("sufficient Sha256 output length to expand");
        assert_ne!(okm, [0u8; 32]);
        // log::info!("hkdf_label:{hkdf_label:?}\n");
        assert_eq!(hkdf_label.len(), hkdf_label_full_len as usize);
        okm
    }

    fn derive_secret(secret: &[u8], label: &str, messages: &[u8]) -> Vec<u8> {
        let mut sha2 = Sha256::new();
        Digest::update(&mut sha2, messages);
        let hash = sha2.finalize();
        Self::hkdf_expand_label(secret, label, &hash, HASH_LEN as u16)
    }

    fn early_secret() -> Vec<u8> {
        Self::hkdf_extract([0; HASH_LEN].as_slice(), [0; HASH_LEN].as_slice())
    }

    // 'salt_for_handshake_traffic_secret' produces salt for deriving handshake secret..
    // hkdf_extract(salt_handshake_traffic_secret, dhe_shared_secret) -> handshake_secret
    fn salt_for_handshake_traffic_secret(prk: &[u8]) -> Vec<u8> {
        Self::derive_secret(prk, "derived", &[])
    }

    fn handshake_traffic_secret(salt_prk: &[u8], dhe_secret: &[u8]) -> Vec<u8> {
        Self::hkdf_extract(salt_prk, dhe_secret)
    }

    fn client_handshake_traffic_secret(salt_prk: &[u8], ch_plus_sh: &[u8]) -> Vec<u8> {
        Self::derive_secret(salt_prk, "c hs traffic", ch_plus_sh)
    }

    fn server_handshake_traffic_secret(salt_prk: &[u8], ch_plus_sh: &[u8]) -> Vec<u8> {
        Self::derive_secret(salt_prk, "s hs traffic", ch_plus_sh)
    }

    // Section 7.3. Traffic Key Calculation. page 95
    // 'key_len' is the length of the key being generated.
    // the purpose value "key" indicates the specific value being generated
    // The value of 'secret' for Handshake record type for server and client is
    // 'server_handshake_traffic_secret', and 'client_handshake_traffic_secret', respectively.
    // The value of 'secret' for Application Data record type is
    // 'server_application_traffic_secret' and 'client_application_traffic_secret', respectively.
    fn sender_write_key(secret: &[u8], key_len: u16) -> Vec<u8> {
        Self::hkdf_expand_label(secret, "key", &[], key_len)
    }

    fn sender_write_iv(secret: &[u8], iv_len: u16) -> Vec<u8> {
        Self::hkdf_expand_label(secret, "iv", &[], iv_len)
    }

    fn salt_for_master_traffic_secret(prk: &[u8]) -> Vec<u8> {
        Self::derive_secret(prk, "derived", &[])
    }

    fn traffic_master_secret(salt_prk: &[u8]) -> Vec<u8> {
        Self::hkdf_extract(salt_prk, &[0; 32])
    }

    // 'ch_plus_sf' is the concatenation of ClientHello upto and including ServerFinished messages
    fn client_application_traffic_secret(salt_prk: &[u8], ch_plus_sf: &[u8]) -> Vec<u8> {
        Self::derive_secret(salt_prk, "c ap traffic", ch_plus_sf)
    }

    // 'ch_plus_sf' is the concatenation of ClientHello upto and including ServerFinished messages
    fn server_application_traffic_secret(salt_prk: &[u8], ch_plus_sf: &[u8]) -> Vec<u8> {
        Self::derive_secret(salt_prk, "s ap traffic", ch_plus_sf)
    }

    fn new(_psk: [u8; HASH_LEN], _dhe_secret: [u8; HASH_LEN]) -> Self {
        Self {}
    }
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct TlsChannel {
    server: String,
    stream: TcpStream,
}

#[allow(dead_code)]
impl TlsChannel {
    pub async fn new(server: &str) -> Result<TlsChannel, Mutter> {
        let server_sock_addresses = server.to_socket_addrs()
                                          .map_err(|_| Mutter::BadNetworkAddress)?;
        for serv_sock_addr in server_sock_addresses {
            let socket = TcpSocket::new_v4().map_err(|_| Mutter::TlsConnection)?;
            if let Ok(sock_stream) = socket.connect(serv_sock_addr).await {
                sock_stream.nodelay().map_err(|_| Mutter::SocketPropertyError)?;
                return Ok(TlsChannel {
                    server: server.to_owned(),
                    stream: sock_stream,
                })
            }
        }
        Err(Mutter::TlsConnection)
    }

    pub async fn readable(&self) -> Result<(), Mutter> {
        self.stream.readable().await
            .map_err(|_| Mutter::TlsChannelReadiness)
            .map(|_| ())
    }

    pub async fn read(&self, mut buf: &mut [u8]) -> Result<usize, Mutter> {
        let mut serv_resp_len: usize = 0;
        loop {
            self.readable().await?;
            return match self.stream.try_read_buf(&mut buf) {
                Ok(0) => {
                    Ok(serv_resp_len)
                }
                Ok(n) => {
                    serv_resp_len += n;
                    continue; // this takes a few minutes to drain the data from the server...
                    // TODO: return as soon as we have data, and keep reading when required.
                    // Ok(serv_resp_len)
                }
                Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                    continue;
                }
                Err(e) => {
                    log::error!("error: {e:#?}");
                    Err(Mutter::StreamError)
                }
            }
        }
    }

    pub async fn write(&self, buf: &[u8]) -> Result<usize, Mutter> {
        let _ = self.stream.writable().await;
        self.stream.try_write(buf)
            .map_err(|_| Mutter::TlsChannelReadiness)
    }

    pub async fn shutdown(&mut self) -> Result<(), Mutter> {
        self.stream.shutdown()
            .await
            .map_err(|_| Mutter::TlsChannelReadiness)
    }
}

pub fn tls_channel_read() {}

// use the following command to run tests defined in the lib, and those in examples.
// RUSTFLAGS="--cfg=release_test -Adead_code -Aunused" cargo test --examples --release -- --show-output
// cargo test --example t3c -- --show-output
#[allow(unused_variables)]
#[cfg(test)]
mod tls13_client_tests {
    use buckle::init_logger;

    use crate::{CryptoRandom, sample};
    use crate::tls3::{CipherSuite, ClientHelloHandshake, Extension};

    #[test]
    fn test_deserialize_01() {
        init_logger(true);
        let random: Vec<u8> = CryptoRandom::<32>::bytes().expect("").to_vec(); //;(64..(64 + 32)).collect();
        let res = ClientHelloHandshake::try_from(random.try_into().unwrap(),
                                                 vec![CipherSuite::TlsChacha20Poly1305Sha256, CipherSuite::TlsAes128GcmSha256],
                                                 vec![Extension::supported_ver_1_3()]
        );
        assert!(res.is_ok());
        let ch = res.unwrap();
        let mut bytes: [u8; 2048] = [0; 2048];
        let res = ch.serialize(&mut bytes[0..]);
        log::info!("{bytes:?}");
        assert!(res.is_ok());
    }

    // #[test]
    fn test_client_hello() {
        init_logger(true);
        let res = ClientHelloHandshake::deserialize(sample::RAW_CLIENT_HELLO);
        let ch = res.unwrap();
        let mut bytes: [u8; 2048] = [0; 2048];
        let res = ch.serialize(&mut bytes[0..]);
        log::info!("{bytes:?}");
        assert!(res.is_ok());
    }
}

#[allow(dead_code)]
mod sample {
    pub(crate) const RAW_CLIENT_HELLO: &[u8] = &[
        0x16, 0x03, 0x03, 0x00, 0xF8, 0x01, 0x00, 0x00, 0xF4, 0x03, 0x03, 0x00, 0x01, 0x02, 0x03,
        0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12,
        0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0xE0,
        0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF,
        0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,
        0xFF, 0x00, 0x08, 0x13, 0x02, 0x13, 0x03, 0x13, 0x01, 0x00, 0xFF, 0x01, 0x00, 0x00, 0xA3,
        0x00, 0x00, 0x00, 0x18, 0x00, 0x16, 0x00, 0x00, 0x13, 0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C,
        0x65, 0x2E, 0x75, 0x6C, 0x66, 0x68, 0x65, 0x69, 0x6D, 0x2E, 0x6E, 0x65, 0x74, 0x00, 0x0B,
        0x00, 0x04, 0x03, 0x00, 0x01, 0x02, 0x00, 0x0A, 0x00, 0x16, 0x00, 0x14, 0x00, 0x1D, 0x00,
        0x17, 0x00, 0x1E, 0x00, 0x19, 0x00, 0x18, 0x01, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01, 0x03,
        0x01, 0x04, 0x00, 0x23, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00,
        0x0D, 0x00, 0x1E, 0x00, 0x1C, 0x04, 0x03, 0x05, 0x03, 0x06, 0x03, 0x08, 0x07, 0x08, 0x08,
        0x08, 0x09, 0x08, 0x0A, 0x08, 0x0B, 0x08, 0x04, 0x08, 0x05, 0x08, 0x06, 0x04, 0x01, 0x05,
        0x01, 0x06, 0x01, 0x00, 0x2B, 0x00, 0x03, 0x02, 0x03, 0x04, 0x00, 0x2D, 0x00, 0x02, 0x01,
        0x01, 0x00, 0x33, 0x00, 0x26, 0x00, 0x24, 0x00, 0x1D, 0x00, 0x20, 0x35, 0x80, 0x72, 0xD6,
        0x36, 0x58, 0x80, 0xD1, 0xAE, 0xEA, 0x32, 0x9A, 0xDF, 0x91, 0x21, 0x38, 0x38, 0x51, 0xED,
        0x21, 0xA2, 0x8E, 0x3B, 0x75, 0xE9, 0x65, 0xD0, 0xD2, 0xCD, 0x16, 0x62, 0x54, ];
}

mod consts {
    pub(crate) const HELLO_RETRY_REQUEST: &[u8] = &[
        0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11,
        0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91,
        0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E,
        0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C
    ];
}

// use the following command to run only this example.
// RUSTFLAGS="-Adead_code -Aunused" cargo run --example t3c -- --show-output
#[tokio::main]
async fn main() -> io::Result<()> {
    let tls13_servers = [
        ("www.india.gov", "www.india.gov.in:443"),
        // ("usa.gov", "usa.gov:443"),
        // ("nsa.gov", "nsa.gov:443"),
        // ("www.mitre.org", "www.mitre.org:443"),
        // ("mozilla.org", "mozilla.org:443"),
        ("letsencrypt.org", "letsencrypt.org:443"),
        //("yourdot.net", "yourdot.net:443"),
        // ("github.com", "github.com:443"), // individually encrypted handshake messages
        // ("facebook.com", "www.facebook.com:443"),
        // ("meta.com", "www.meta.com:443"),
        ("microsoft.com", "microsoft.com:443"), // individually encrypted handshake messages
        //("lobste.rs", "lobste.rs:443"),  // individually encrypted handshake messages
        // ("google.com", "www.google.com:443"), // sequence of handshake messages encrypted in one block, one flight.
        // ("twitter.com", "twitter.com:443"), // sequence of handshake messages encrypted in one block, one flight.
        ("apple.com", "apple.com:443"), // sequence of handshake messages encrypted in one block, one flight.
        // ("stackexchange.com", "stackexchange.com:443"), // sequence of handshake messages encrypted in one block, one flight.
        // ("news.ycombinator.com", "news.ycombinator.com:443"), // no support for TLSv1.3
        // ("spacex.com", "www.spacex.com:443"), // TODO: support ecdhe with secp256r1.
        // ("whatsapp.com", "www.whatsapp.com:443")
    ];

    init_logger(true);
    for (server_name, server) in tls13_servers {
        log::info!("");
        let serv_stream = TlsChannel::new(server).await;
        log::info!("Trying {server}");
        // section 4.4.1. The Transcript Hash, page 63.
        // Many of the cryptographic computations in TLS make use of a
        //    transcript hash.  This value is computed by hashing the concatenation
        //    of each included handshake message, including the handshake message
        //    header carrying the handshake message type and length fields, but not
        //    including record layer headers.
        let mut handshake_msg_traffic_ctx: Vec<u8> = Vec::new();
        if let Ok(mut chan) = serv_stream {
            log::info!("Connected {server}");
            chan.stream.writable().await?;
            let random: Vec<u8> = CryptoRandom::<32>::bytes().expect("").to_vec();
            let x25519_key_pair = X25519KeyPair::default();
            let key_share = x25519_key_pair.public_bytes();
            let ch_msg_len: usize;
            {
                let res = ClientHelloHandshake::try_from(random.try_into().unwrap(),
                                                         vec![
                                                             CipherSuite::TlsAes128GcmSha256,
                                                             // CipherSuite::TlsChacha20Poly1305Sha256,
                                                             //CipherSuite::TlsAes128CcmSha256,
                                                             //CipherSuite::TlsAes256GcmSha384,
                                                             //CipherSuite::TlsAes128CcmSha256,
                                                         ],
                                                         vec![
                                                             Extension::server_name(server_name),
                                                             Extension::supported_ver_1_3(),
                                                             Extension::supported_group_x25519(),
                                                             Extension::signature_algorithm_ed25519(),
                                                             Extension::ed25519_key_share(key_share),
                                                         ]
                );
                assert!(res.is_ok());
                let ch = res.unwrap();
                let mut bytes: [u8; 1024] = [0; 1024];
                bytes.fill(0);
                ch_msg_len = ch.serialize(&mut bytes).expect("valid ClientHello for serialization");
                let n = chan.write(&bytes[0..ch_msg_len]).await.expect("sending ClientHello");
                handshake_msg_traffic_ctx.extend_from_slice(&bytes[5..ch_msg_len]);
                assert_eq!(handshake_msg_traffic_ctx.len() + 5, n);
                log::info!("sending {ch_msg_len} bytes to {server_name}; wrote {n} bytes");
            }

            {
                let mut msg_buf = [0; 8 * 1024];
                msg_buf.fill(0);
                let serv_resp_len: usize = chan.read(msg_buf.as_mut_slice()).await.expect("ServerHello and encrypted messages");
                assert!(serv_resp_len < msg_buf.len());
                log::info!("ServerHello processed.");
                if [0x16, 0x03, 0x03] == msg_buf[0..3] {
                    assert_eq!(msg_buf[5], 0x2); // server_hello
                    assert_eq!(msg_buf[9..11], [0x3, 0x3]); // legacy_tls_version

                    // let mut shm_reader = ServerHelloMsgReader::new(&msg_buf);
                    let mut shm_reader = ServerHelloMsgReader::new(&msg_buf);
                    let (shm, sh_len) = match ServerHelloHandshake::deserialize(&mut shm_reader) {
                        Ok((shm, sh_len)) => (shm, sh_len),
                        _ => {
                            log::warn!("Handshake with {server_name} is aborted.\n");
                            continue
                        }
                    };
                    assert_eq!(shm.cipher_suite, CipherSuite::TlsAes128GcmSha256);
                    assert_ne!(shm.random, consts::HELLO_RETRY_REQUEST);
                    assert!(sh_len > 0);
                    {
                        assert!(shm.legacy_session_id.is_none());
                        assert_eq!(shm.fragment_len as usize, sh_len - 5);
                        assert_eq!(handshake_msg_traffic_ctx.len(), ch_msg_len - 5);
                        handshake_msg_traffic_ctx.extend_from_slice(&msg_buf[5..sh_len]);
                        assert_eq!(ch_msg_len - 5 + sh_len - 5, handshake_msg_traffic_ctx.len());
                        // calculate ECDHE shared secret
                        let server_ecdhe_pk_bytes = shm.x25519_key().expect("require a valid x25519 key in ServerHello");
                        let ecdhe_secret: SharedSecret = x25519_key_pair.dh(server_ecdhe_pk_bytes);
                        assert_ne!(ecdhe_secret.as_bytes(), &[0u8; 32]);
                        // calculate the key schedule
                        let early_secret = KeySchedule::<32>::early_secret();
                        assert_eq!(early_secret.len(), 32); // HASH_LEN
                        let salt_hs_traffic = KeySchedule::<32>::salt_for_handshake_traffic_secret(&early_secret);
                        let hs_secret = KeySchedule::<32>::handshake_traffic_secret(&salt_hs_traffic,
                                                                                    ecdhe_secret.as_bytes());
                        let server_hs_secret = KeySchedule::<32>::server_handshake_traffic_secret(&hs_secret,
                                                                                                  &handshake_msg_traffic_ctx);
                        let server_hs_key = KeySchedule::<32>::sender_write_key(&server_hs_secret, 16);
                        let server_hs_iv = KeySchedule::<32>::sender_write_iv(&server_hs_secret, 12);
                        // log::info!("\nserver_hs_key_len = {}, server_hs_iv_len = {}", server_hs_key.len(), server_hs_iv.len());

                        log::info!("server_resp_len = {serv_resp_len}");
                        let rcs: (Option<ChangeCipherSpecMsg>, usize) =
                            ChangeCipherSpecMsg::deserialize(&msg_buf[sh_len..serv_resp_len]).expect("change_cipher_spec");
                        assert!((rcs.0.is_none() && rcs.1 == 0) || (rcs.0.is_some() && rcs.1 == 6));
                        let mut app_data_start = sh_len + rcs.1;
                        let mut count_rec = 0u8;
                        let aes_decryption_key = Key::<Aes128Dec>::from_slice(&server_hs_key);
                        assert_eq!(aes_decryption_key.len(), 16);
                        let cipher = Aes128Gcm::new(aes_decryption_key);
                        let mut handshake_messages = HandshakeMessageBuilder::default();
                        let mut handshake_finished = false;
                        while app_data_start < serv_resp_len {
                            //let buf_len = msg_buf.len();
                            let appl_data_len = ApplicationDataMsg::deserialize(&msg_buf[app_data_start..serv_resp_len]).expect("application_data message");
                            // log::info!("appl_data_pre8 = {:?}, app_data_cursor = {app_data_start}, appl_data_len = {}", &msg_buf[app_data_start..app_data_start+8], appl_data_len);
                            if appl_data_len == 0 {
                                break
                            }
                            {
                                assert!(appl_data_len > 5);
                                // decrypt the data
                                // update nonce with the record count
                                let mut nonce_bytes: [u8; 12] = [0; 12];
                                nonce_bytes.copy_from_slice(&server_hs_iv);
                                nonce_bytes[11] ^= count_rec;
                                let nonce = Nonce::from_slice(&nonce_bytes);
                                {
                                    let mut plain_text = Vec::from(&msg_buf[app_data_start + 5..app_data_start + appl_data_len]);
                                    // section 5.2. Record Payload Protection, page 81.
                                    // additional data - first five bytes of the record
                                    let ad = &msg_buf[app_data_start..app_data_start + 5];
                                    let decrypt_res = cipher.decrypt_in_place(nonce, ad, (&mut plain_text) as &mut dyn aead::Buffer);
                                    if decrypt_res.is_ok() && !handshake_finished {
                                        // log::info!("\n\n message_ctx before Certificate {:?}\n\n", &handshake_msg_traffic_ctx);
                                        if let Ok((done, builder)) = handshake_messages.update(plain_text, &mut handshake_msg_traffic_ctx) {
                                            if done {
                                                //log::info!("handshake_message_builder - successfully serialized");
                                                if builder.msg_type == HandshakeType::Finished {
                                                    handshake_finished = true;
                                                    log::info!("\thandshake_message_builder - Finish processed"); // section 4.4.4. Finished, page 72
                                                    let mut sha256 = Sha256::new();
                                                    Digest::update(&mut sha256, &handshake_msg_traffic_ctx);
                                                    let transcript_hash = sha256.finalize();
                                                    let finished_key =
                                                        GenericArray::<_, U32>::clone_from_slice(
                                                            &KeySchedule::<32>::hkdf_expand_label(&server_hs_secret, "finished", &[], 32));
                                                    let mut hmac_sha256 = <Hmac<Sha256> as KeyInit>::new_from_slice(&finished_key).expect("hmac");
                                                    hmac_sha256.update(&transcript_hash);
                                                    let x = hmac_sha256.finalize();
                                                    log::info!("verify_data = {:?}", x.into_bytes());
                                                }
                                            } else {
                                                //log::info!("\thandshake_message_builder - builder in progress");
                                            }
                                        } else {
                                            panic!("handshake_message_builder - not a handshake message...");
                                        }
                                    } else if handshake_finished {
                                        let _salt_master_traffic = KeySchedule::<32>::salt_for_master_traffic_secret(&early_secret);
                                        let _master_secret = KeySchedule::<32>::traffic_master_secret(&_salt_master_traffic);
                                        // let server_traffic_master_secret = KeySchedule::<32>::server_application_traffic_secret(&master_secret,
                                        log::info!("\tMessage following Finished Message {:?}...to be decrypted!!", plain_text);
                                    }
                                }
                                app_data_start += appl_data_len;
                                count_rec += 1;
                                // log::info!("next_record_count: {count_rec}, next_app_data_cursor = {app_data_start}");
                            }
                        }
                        assert_eq!(serv_resp_len, app_data_start);
                        log::info!("Final Cursor pos: {app_data_start}/{serv_resp_len}\n");
                        msg_buf.fill(0);
                        let serv_resp_len = chan.read(msg_buf.as_mut_slice()).await.expect("zero or more bytes of data");
                        if serv_resp_len > 0 {
                            log::info!("read {serv_resp_len} bytes from {server} again!");
                        }
                    }
                    // assert_eq!(serv_hello_enc_ext[shm_reader.pos()], 8);
                } else if [0x15, 0x03, 0x03] == msg_buf[0..3] {
                    assert_eq!(serv_resp_len, 7);
                    // log::info!("\tSH response bytes; {:?}", &serv_hello_enc_ext[0..serv_resp_len]);
                    let alert_len = (msg_buf[3] as usize) << 8 | msg_buf[4] as usize;
                    assert_eq!(alert_len, serv_resp_len - 5);
                    assert!((1u8..=2).contains(&msg_buf[5]));
                    let (alert_level, alert_desc) = (msg_buf[5], msg_buf[6]);
                    match alert_level {
                        1 => {
                            log::info!("server warning: {}", alert_desc);
                        },
                        2 => {
                            log::info!("server error: {}", alert_desc);
                            match alert_desc.try_into().expect("unknown alert desc!") {
                                AlertDesc::RecordOverflow => log::error!("Error - record overflow."),
                                AlertDesc::HandshakeFailure => log::error!("Error - handshake failure."),
                                AlertDesc::DecodeError => log::error!("Error - ClientHello message decoding error."),
                                AlertDesc::ProtocolVersion => log::error!("Error - TLSv1.3 not supported."),
                                AlertDesc::InternalError => log::error!("Error - internal error (Server)."),
                                AlertDesc::MissingExtension => log::error!("Error - missing extension."),
                                AlertDesc::UnsupportedExtension => log::error!("Error - unsupported extension."),
                                AlertDesc::UnrecognizedName => log::error!("Error - unsupported extension."),
                                _ => log::error!("unhandled alert desc!"),
                            }
                        },
                        _ => panic!("unknown alert level and desc: ({alert_level}, {alert_desc})"),
                    }
                    log::error!("ClientHello failed for {server_name}\n");
                } else {
                    log::error!("Error: No response from {server_name} for ClientHello\n");
                }
            }
            let _ = chan.shutdown().await;
        }
    }
    Ok(())
}

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
struct HandshakeMessageBuilder {
    size: usize,
    copied: usize,
    msg_type: HandshakeType,
}

#[allow(dead_code)]
impl HandshakeMessageBuilder {
    fn reset(&mut self) {
        self.size = 0;
        self.copied = 0;
        self.msg_type = HandshakeType::Bad;
    }

    fn required(&self) -> usize {
        self.size - self.copied
    }

    fn update(&mut self, t: Vec<u8>, traffic_ctx: &mut Vec<u8>) -> Result<(bool, HandshakeMessageBuilder), Mutter> {
        let zero_pad_len = t.iter().rev().take_while(|&c| *c == 0).fold(0, |acc, _| acc + 1);
        let mut i = 0;
        while i < t.len() {
            let msg_begin_pos;
            let available_msg_len;
            if self.required() == 0 { // we are copying a fresh message record
                let msg_type = t[i].into();
                if msg_type == HandshakeType::Bad {
                    log::error!("\tHandshakeMessageBuilder::update - Not a known HandshakeMessage: {:?}", &t[i..i+8]);
                    return Err(Mutter::UnsupportedHandshakeMessageType)
                };
                msg_begin_pos = i;
                self.reset();
                let len = ((t[i + 1] as usize) << 16) | ((t[i + 2] as usize) << 8) | t[i + 3] as usize;
                /*if len == 0 || (len > (2usize << 24) + 255) {
                    log::error!("HandshakeMessages::next - message size larger than the permitted size");
                    return Err(Mutter::MsgSizeInvalid)
                }*/
                self.msg_type = msg_type;
                self.size = len;
                i += 4;
                available_msg_len = min(t.len() - i, self.required());

                match msg_type {
                    HandshakeType::EncryptedExtensions => {
                        log::info!("HandshakeMessageBuilder::update - EncryptedExtension");
                    },
                    HandshakeType::Certificate => {
                        log::info!("HandshakeMessageBuilder::update - Certificate");
                    },
                    HandshakeType::CertificateVerify => {
                        log::info!("HandshakeMessageBuilder::update - CertificateVerify");
                    },
                    HandshakeType::CertificateRequest => {
                        log::info!("HandshakeMessageBuilder::update - CertificateRequest");
                    },
                    HandshakeType::Finished => {
                        log::info!("HandshakeMessageBuilder::update - Finished");
                        assert_eq!(self.size, 32); // TODO: use the size of the selected hash primitive
                    },
                    _ => {
                        log::info!("HandshakeMessages::next - Unsupported HandshakeMessage.");
                    }
                }
            } else { // we are updating an incomplete message record
                assert!(self.copied > 0 && self.copied < self.size);
                msg_begin_pos = i;
                available_msg_len = min(t.len() - i, self.required());
            }
            self.copied += available_msg_len;
            // messages except Finished are part of the message context
            assert!(i + available_msg_len <= t.len());
            if self.msg_type == HandshakeType::Finished {
                log::info!("Finish mac = {:?}", &t[i-4..i + available_msg_len]);
            }
            let _ctx_len_ = traffic_ctx.len();
            assert!(_ctx_len_ > 0);
            if self.msg_type == HandshakeType::Certificate ||
                self.msg_type == HandshakeType::CertificateVerify ||
                self.msg_type == HandshakeType::EncryptedExtensions {
                traffic_ctx.extend_from_slice(&t[msg_begin_pos..i + available_msg_len]);
                // log::info!("Traffic Ctx for {:?} {:?}", self.msg_type, &t[msg_begin_pos..i + 8]);
                // assert_eq!(_ctx_len_ + available_msg_len + 4, traffic_ctx.len());
            }
            i += available_msg_len;

            // I notice that meta and facebook have an incorrect zer0-size extensions field
            // after the CertificateEntry structure.
            if self.msg_type == HandshakeType::Certificate {
                // section 4.4.2, Certificate, page 64
                // grab the extensions in the CertificateEntry
                let _k_ = t[i..t.len()].iter().take_while(|&c| *c == 0).fold(0, |acc, _| acc + 1);
                assert!(_k_ <= 2);
                log::info!("\nCertificate Entry - skipped {_k_} bytes\n");
                if _k_ > 0 {
                    traffic_ctx.extend_from_slice(&t[i..i + _k_]);
                    i += _k_;
                }
            }

            // in case the plaintext length is less than the actual message length, go and get
            // the next record. (Note: the next record needs to be decrypted).
            if self.copied < self.required() {
                // indicate this message is incomplete, and needs the next fragment...
                log::info!("require more data to complete {:?}", self);
                return Ok((false, self.clone()))
            }

            assert!(i <= t.len());
            if i == t.len() - zero_pad_len - 1 && t[i] == RecordContentType::Handshake as u8 {
                // traffic_ctx.push(t[i]);
                return Ok((true, self.clone()))
            }
        }
        Ok((true, self.clone()))
    }
}