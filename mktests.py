#! /usr/bin/env python3

# This script uses the jq255 implementation (jq255.py) to generate test
# vectors. One command-line argument:
#    jq255e    make test vectors for jq255e
#    jq255s    make test vectors for jq255s
#    all       make test vectors for both jq255e and jq255s
# If no argument is provided, then 'all' is assumed.
#
# Test vectors are produced on standard output. Test vector production
# is deterministic (you always get the same vectors for a given curve).
# WARNING: production of the Monte-Carlo point multiplication vectors
# is computationally intensive and requires a few minutes.

import importlib
import sys
import hashlib
import jq255

# Make test vectors for decoding tests.
def mktests_decode(curve):
    print('# Decode test vectors for ' + curve.name)
    print('# These values can all be decoded.')
    print('0000000000000000000000000000000000000000000000000000000000000000')
    rs = hashlib.sha256(curve.bname + b'-test-decode').digest()
    ap = -2*curve.a
    bp = curve.a**2 - 4*curve.b
    for i in range(0, 20):
        while True:
            rs = hashlib.sha256(rs).digest()
            rt = int.from_bytes(rs, byteorder='big')
            u = curve.K(rt)
            if (bp*u**4 + ap*u**2 + 1).is_square():
                break
        val = bytes(u)
        print(val.hex())
        # Try decoding, it should work.
        P = curve.Decode(val)
        val2 = bytes(P)
        if val != val2:
            raise Exception('Decode/encode failed (different bytes)')
    print('')

    print('# These values cannot be decoded (u is out of range).')
    for i in range(0, 20):
        if i == 0:
            # First test checks that values just above the modulus are
            # properly rejected, instead of being implicitly reduced.
            iu = curve.K.m + 1
            while True:
                u = curve.K(iu)
                if (bp*u**4 + ap*u**2 + 1).is_square():
                    break
                iu += 1
        else:
            # Even-numbered tests verify that the top bit is checked but
            # not ignored; odd-numbered tests verify that the whole value
            # is not implicitly reduced.
            while True:
                rs = hashlib.sha256(rs).digest()
                iu = int.from_bytes(rs, byteorder='big')
                if (i & 1) == 0:
                    if iu < 2**255:
                        u = curve.K(iu)
                        iu += 2**255
                    else:
                        u = curve.K(iu - 2**255)
                else:
                    if iu < 2**255:
                        iu += 2**255
                    u = curve.K(iu)
                if (bp*u**4 + ap*u**2 + 1).is_square():
                    break
        val = iu.to_bytes(32, byteorder='little')
        print(val.hex())
        # Try decoding, it should fail.
        good = False
        try:
            curve.Decode(val)
        except Exception:
            good = True
        if not good:
            raise Exception('Decoding should have failed')
    print('')

    print('# These values cannot be decoded (u matches no point).')
    for i in range(0, 20):
        while True:
            rs = hashlib.sha256(rs).digest()
            rt = int.from_bytes(rs, byteorder='big')
            u = curve.K(rt)
            if not((bp*u**4 + ap*u**2 + 1).is_square()):
                break
        val = bytes(u)
        print(val.hex())
        # Try decoding, it should fail.
        good = False
        try:
            curve.Decode(val)
        except Exception:
            good = True
        if not good:
            raise Exception('Decoding should have failed')
    print('')

# Make test vectors for map-to-curve tests.
def mktests_pointmap(curve):
    print('# Map-to-curve test vectors for ' + curve.name)
    print('# Each group of two values is: input bytes, mapped point')
    rs = hashlib.sha256(curve.bname + b'-test-map').digest()
    for i in range(0, 40):
        rs = hashlib.sha256(rs).digest()
        if i == 0:
            bb = bytearray(32)
            if not curve.a.is_zero():
                bb[0] = 1
        else:
            bb = rs
        P = curve.MapToCurve(bb)
        if i == 0:
            if not P.is_neutral():
                raise Exception('zero should be mapped to neutral')
        else:
            # Sanity checks on the point.
            if P.Z.is_zero():
                raise Exception('invalid point')
            e = P.E / P.Z
            u = P.U / P.Z
            if P.U**2 != P.T*P.Z:
                raise Exception('invalid point')
            if e**2 != curve.bp*u**4 + curve.ap*u**2 + curve.K.one:
                raise Exception('invalid point')
            x = (e + curve.K.one - curve.a*u**2) / (2*u**2)
            w = curve.K.one / u
            if w**2*x != x**2 + curve.a*x + curve.b:
                raise Exception('invalid point')
            if x.is_square():
                raise Exception('mapped to an r-torsion point')
        print(bb.hex())
        print(bytes(P).hex())
        print('')

# Make test vectors for point addition.
def mktests_add(curve):
    print('# Point addition test vectors for ' + curve.name)
    print('# Each group of six values is: P1, P2, P1+P2, 2*P1, 2*P1+P2, 2*P1+2*P2')
    rs = hashlib.sha256(curve.bname + b'-test-add').digest()
    for i in range(0, 20):
        rs = hashlib.sha256(rs).digest()
        rt = int.from_bytes(rs, byteorder='big')
        P1 = curve.G * rt
        rs = hashlib.sha256(rs).digest()
        rt = int.from_bytes(rs, byteorder='big')
        P2 = curve.G * rt
        P3 = P1 + P2
        P4 = P1 + P1
        P5 = P4 + P2
        P6 = P3 + P3
        print(bytes(P1).hex())
        print(bytes(P2).hex())
        print(bytes(P3).hex())
        print(bytes(P4).hex())
        print(bytes(P5).hex())
        print(bytes(P6).hex())
        print('')

# Make test vectors for point multiplication.
# Scalars may range up to the full 256-bit range.
def mktests_pointmul(curve):
    print('# Point multiplication test vectors for ' + curve.name)
    print('# Each group of three values is: P, n, n*P')
    print('# (multiplier n may range up to 2**256-1)')
    rs = hashlib.sha256(curve.bname + b'-test-pointmul').digest()
    for i in range(0, 20):
        rs = hashlib.sha256(rs).digest()
        rt = int.from_bytes(rs, byteorder='big')
        P1 = curve.G * rt
        rs = hashlib.sha256(rs).digest()
        rt = int.from_bytes(rs, byteorder='big')
        P3 = P1 * rt
        print(bytes(P1).hex())
        print(rt.to_bytes(32, byteorder='little').hex())
        print(bytes(P3).hex())
        print('')

# Make extra test vector for point multiplication.
def mktests_MC_pointmul(curve):
    print('# Monte-Carlo test vectors for ' + curve.name)
    print('# Starting point P[0] = (2**120)*G.')
    print('# Then, for i = 1...10000 (inclusive): P[i] = int(P[i-1].encode())*P[i-1]')
    print('# Below are P[0], P[1000], P[2000],... P[10000]')
    P = curve.G * (2**120)
    print(bytes(P).hex(), flush=True)
    for i in range(1, 10001):
        m = int.from_bytes(bytes(P), byteorder='little')
        P = P * m
        if i % 1000 == 0:
            print(bytes(P).hex(), flush=True)
    print('')

def mktests_algs(curve):
    # Keygen tests
    print('# Keygen tests for ' + curve.name)
    print('# For i = 0..19, keygen with SHAKE256((byte)i) as source.')
    print('# Each group of two values is the private/public key pair.')
    for i in range(0, 20):
        sh = hashlib.shake_256()
        sh.update(int(i).to_bytes(1, 'little'))
        sk = jq255.Keygen(curve, sh)
        pk = jq255.MakePublic(curve, sk)
        print(bytes(sk).hex())
        print(bytes(pk).hex())
        print('')

    # Hash-to-curve tests
    print('# Hash-to-curve (raw) tests for ' + curve.name)
    print('# For i = 0..99, hash-to-curve using as data the first i bytes')
    print('# of the sequence 00 01 02 03 .. 62  (raw data, no hash function)')
    data = bytearray()
    for i in range(0, 100):
        P = jq255.HashToCurve(curve, b'', data)
        data.append(i)
        print(bytes(P).hex())
    print('')

    print('# Hash-to-curve (pre-hashed) tests for ' + curve.name)
    print('# For i = 0..10, hash-to-curve using as data the BLAKE2s hash of')
    print('# a single byte of value i.')
    data = bytearray()
    for i in range(0, 10):
        sh = hashlib.blake2s()
        sh.update(i.to_bytes(1, byteorder='little'))
        data = sh.digest()
        P = jq255.HashToCurve(curve, jq255.HASHNAME_BLAKE2S, data)
        print(bytes(P).hex())
    print('')

    # ECDH tests
    print('# ECDH tests for ' + curve.name)
    print('# Each group of five values is:')
    print('#   private key')
    print('#   public peer point (valid)')
    print('#   secret from ECDH with valid peer point')
    print('#   public peer point (invalid)')
    print('#   secret from ECDH with invalid peer point')
    for i in range(0, 20):
        # Valid test.
        rng = hashlib.shake_256()
        rng.update(curve.bname)
        rng.update(b'-test-ECDH-self-')
        rng.update(int(i).to_bytes(2, 'little'))
        sk_self = jq255.Keygen(curve, rng)
        pk_self = jq255.MakePublic(curve, sk_self)
        rng = hashlib.shake_256()
        rng.update(curve.bname)
        rng.update(b'-test-ECDH-peer-')
        rng.update(int(i).to_bytes(2, 'little'))
        sk_peer = jq255.Keygen(curve, rng)
        pk_peer = jq255.MakePublic(curve, sk_peer)
        ok, secret = jq255.ECDH(sk_self, pk_self, pk_peer, 32)
        if not ok:
            raise Exception('ECDH failed')
        # Try again with decoding inside the function.
        ok2, secret2 = jq255.ECDH(sk_self, pk_self, bytes(pk_peer), 32)
        if not ok2:
            raise Exception('ECDH failed (with decoding)')
        if secret2 != secret:
            raise Exception('ECDH wrong secret (with decoding)')
        # Verify that the peer would get the same value.
        ok3, secret3 = jq255.ECDH(sk_peer, pk_peer, pk_self, 32)
        if not ok3:
            raise Exception('ECDH failed (reverse)')
        if secret3 != secret:
            raise Exception('ECDH wrong secret (reverse)')
        print(bytes(sk_self).hex())
        print(bytes(pk_peer).hex())
        print(bytes(secret).hex())

        # Invalid test.
        j = 0
        while True:
            rng = hashlib.shake_256()
            rng.update(curve.bname)
            rng.update(b'-test-ECDH-peer-')
            rng.update(int(i).to_bytes(2, 'little'))
            rng.update(int(j).to_bytes(4, 'little'))
            u = curve.K.DecodeReduce(rng.digest(32))
            if not((curve.bp*u**4 + curve.ap*u**2 + curve.K.one).is_square()):
                break
            j += 1
        # We use the binary encoding of the peer public key, so that the
        # ECDH() function applies the alternate secret generation in case
        # of decoding failure.
        ok, secret = jq255.ECDH(sk_self, pk_self, bytes(u), 32)
        if ok:
            raise Exception('ECDH should have failed')
        print(bytes(u).hex())
        print(bytes(secret).hex())
        print('')

    # Signature tests
    print('# Signature tests for ' + curve.name)
    print('# Each group of five values is:')
    print('#   private key')
    print('#   public key')
    print('#   seed ("-" for an empty seed)')
    print('#   data (BLAKE2s of "sample X" with X = 0, 1,...)')
    print('#   signature')
    for i in range(0, 20):
        rng = hashlib.shake_256()
        rng.update(curve.bname)
        rng.update(b'-test-sign-sk-')
        rng.update(i.to_bytes(2, 'little'))
        sk = jq255.Keygen(curve, rng)
        pk = jq255.MakePublic(curve, sk)
        rng.update(curve.bname)
        rng.update(b'-test-sign-seed-')
        rng.update(i.to_bytes(2, 'little'))
        seed = rng.digest(i)
        h = hashlib.blake2s()
        h.update('sample {0}'.format(i).encode('utf-8'))
        hv = h.digest()
        sig = jq255.Sign(sk, pk, jq255.HASHNAME_BLAKE2S, hv, seed)
        if not(jq255.Verify(pk, sig, jq255.HASHNAME_BLAKE2S, hv)):
            raise Exception("Cannot verify signature!")
        if jq255.Verify(pk, sig, jq255.HASHNAME_SHA3_256, hv + b'.'):
            raise Exception("Signature verification should have failed!")
        print(bytes(sk).hex())
        print(bytes(pk).hex())
        if len(seed) == 0:
            print('-')
        else:
            print(seed.hex())
        print(hv.hex())
        print(sig.hex())
        print('')

if len(sys.argv) >= 2:
    name = sys.argv[1].lower()
else:
    name = 'all'

if name == 'jq255e' or name == 'all':
    mktests_decode(jq255.Jq255e)
    mktests_pointmap(jq255.Jq255e)
    mktests_add(jq255.Jq255e)
    mktests_pointmul(jq255.Jq255e)
    mktests_MC_pointmul(jq255.Jq255e)
    mktests_algs(jq255.Jq255e)
if name == 'jq255s' or name == 'all':
    mktests_decode(jq255.Jq255s)
    mktests_pointmap(jq255.Jq255s)
    mktests_add(jq255.Jq255s)
    mktests_pointmul(jq255.Jq255s)
    mktests_MC_pointmul(jq255.Jq255s)
    mktests_algs(jq255.Jq255s)
