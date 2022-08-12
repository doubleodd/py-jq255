#! /usr/bin/env python3

# This is the reference implementation for groups jq255e and jq255s. It
# also includes functions for key exchange (ECDH), signature generation
# and verification (Schnorr signatures), and hash-to-curve.
#
# WARNING: This implementation is mathematically correct, but not secure
# as an implementation: it makes no effort at mitigating side-channel
# leaks (e.g. computation time). It is also not much optimized. The
# intended usage is production of test vectors, and exploration of
# addition formulas. Do NOT use it in production code.
#
# This file contains several classes and variables. In appearance order:
#
#   Zmod                     generic class for computing modulo a given integer
#
#   GF255e, GF255s           base fields for curve jq255e and jq255s
#
#   Scalar255e, Scalar255s   fields for scalars (integers modulo the group
#                            order, which is prime)
#
#   Jq255Curve               base class for curve instances
#
#   Jq255e, Jq255s           instances for the two curves jq255e and jq255s
#
# All this code is meant for Python 3.4+.

# =========================================================================
# Custom implementation of modular integers.
#
# This mimics Sage syntax. For a modulus m, the ring of integers modulo
# m is defined as Zmod(m). A value is obtained by "calling" (function
# call syntax) the ring on an integer (or anything that can be
# transtyped into an integer); that integer is internally reduced.
# Values are immutable. When converted to a string or formatted, they
# behave like plain integers with a value in the 0..m-1 range.
#
# Inversion works only for an odd modulus. Square root extraction works
# only for a prime modulus equal to 3, 5 or 7 modulo 8 (i.e. an odd prime
# which is not equal to 1 modulo 8); if the modulus is not prime, then
# incorrect results will be returned.

class Zmod:
    def __init__(self, m):
        """
        Initialize for the provided modulus. The modulus must be convertible
        to a positive integer of value at least 2.
        """
        m = int(m)
        if m < 2:
            raise Exception('invalid modulus')
        self.m = m
        self.encodedLen = (m.bit_length() + 7) >> 3
        self.zero = Zmod.Element(self, 0)
        self.one = Zmod.Element(self, 1)
        self.minus_one = Zmod.Element(self, m - 1)

    def __call__(self, x):
        """
        Make a ring element. If x is already an element of this ring,
        then it is returned as is. Otherwise, x is converted to an integer,
        which is reduced modulo the ring modulus, and used to make a new
        value.
        """
        if isinstance(x, Zmod.Element) and (x.ring is self):
            return x
        return Zmod.Element(self, int(x) % self.m)

    def Decode(self, bb):
        """
        Decode an element from bytes (exactly the number of bytes matching
        the modulus length). Unsigned little-endian convention is used.
        If the value is not lower than the modulus, an exception is thrown.
        """
        if len(bb) != self.encodedLen:
            raise Exception('Invalid encoded value (wrong length = {0})'.format(len(bb)))
        x = int.from_bytes(bb, byteorder='little')
        if x >= self.m:
            raise Exception('Invalid encoded value (not lower than modulus)')
        return Zmod.Element(self, x)

    def DecodeReduce(self, bb):
        """
        Decode an element from bytes. All provided bytes are read, in
        unsigned little-endian convention; the value is then reduced
        modulo the ring modulus.
        """
        x = int.from_bytes(bb, byteorder='little')
        return Zmod.Element(self, x % self.m)

    class Element:
        def __init__(self, ring, value):
            self.ring = ring
            self.x = int(value)

        def __getattr__(self, name):
            if name == 'modulus':
                return self.ring.m
            else:
                raise AttributeError()

        def __int__(self):
            """
            Conversion to an integer returns the value in the 0..m-1 range.
            """
            return self.x

        def valueOfOther(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring is b.ring:
                    return b.x
                if self.ring.m != b.ring.m:
                    raise Exception('ring mismatch')
                return b.x
            elif isinstance(b, int):
                return b % self.ring.m
            else:
                return False

        def __add__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x + b)

        def __radd__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b + self.x)

        def __sub__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x - b)

        def __rsub__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b - self.x)

        def __neg__(self):
            return self.ring(-self.x)

        def __mul__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x * b)

        def __rmul__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b * self.x)

        def __truediv__(self, y):
            # This function works only if the modulus is odd.
            # If the divisor is not invertible, then we return 0.
            #
            # We use a binary GCD. Invariants:
            #   a*x = u*y mod m
            #   b*x = v*y mod m
            # The GCD ends with b = 1, in which case v = x/y mod m.
            a = self.valueOfOther(y)
            if a is False:
                return NotImplemented
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported division: even modulus')
            b = m
            u = self.x
            v = 0
            while a != 0:
                if (a & 1) == 0:
                    a >>= 1
                    if (u & 1) != 0:
                        u += m
                    u >>= 1
                else:
                    if a < b:
                        a, b = b, a
                        u, v = v, u
                    a -= b
                    if u < v:
                        u += m
                    u -= v
            # Note: if the divisor is zero, then we immediately arrive
            # here with v = 0, which is what we want.
            return self.ring(v)

        def __rtruediv__(self, y):
            return self.ring(y).__truediv__(self)

        def __floordiv__(self, y):
            return self.__truediv__(y)

        def __rfloordiv__(self, y):
            return self.ring(y).__truediv__(self)

        def __pow__(self, e):
            # We do not assume that the modulus is prime; therefore, we
            # cannot reduce the exponent modulo m-1.
            e = int(e)
            if e == 0:
                return self.ring.one
            t = self
            if e < 0:
                t = t.ring.one / t
                e = -e
            r = self
            elen = e.bit_length()
            for i in range(0, elen - 1):
                j = elen - 2 - i
                r *= r
                if ((e >> j) & 1) != 0:
                    r *= self
            return r

        def __lshift__(self, n):
            n = int(n)
            if n < 0:
                raise Exception('negative shift count')
            return self.ring(self.x << n)

        def __rshift__(self, n):
            n = int(n)
            if n < 0:
                raise Exception('negative shift count')
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported right shift: even modulus')
            t = self.x
            while n > 0:
                if (t & 1) != 0:
                    t += m
                t >>= 1
                n -= 1
            return self.ring(t)

        def __eq__(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring.m != b.ring.m:
                    return False
                return self.x == b.x
            else:
                return self.x == int(b)

        def __ne__(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring.m != b.ring.m:
                    return True
                return self.x != b.x
            else:
                return self.x != int(b)

        def __repr__(self):
            return self.x.__repr__()

        def __str__(self):
            return self.x.__str__()

        def __format__(self, fspec):
            return self.x.__format__(fspec)

        def __bytes__(self):
            return self.x.to_bytes(self.ring.encodedLen, byteorder='little')

        def sqrt(self):
            """
            Compute a square root of the current value. If the value is
            not a square, this returns False. The returned square root is
            normalized: its least significant bit (as an integer in the
            0..m-1 range) is zero.

            WARNING: square root extraction assumes that the modulus is
            a prime integer. It works only for a modulus equal to 3, 5
            or 7 modulo 8.
            """
            m = self.ring.m
            if (m & 3) == 3:
                s = self**((m + 1) >> 2)
            elif (m & 7) == 5:
                # Atkin's formulas:
                #   b <- (2*a)^((m-5)/8)
                #   c <- 2*a*b^2
                #   return a*b*(c - 1)
                b = (self << 1)**((m - 5) >> 3)
                c = (self*b*b) << 1
                s = self*b*(c - 1)
            else:
                raise Exception('Unsupported square root for this modulus')
            if (s * s).x != self.x:
                return False
            if (s.x & 1) != 0:
                s = -s
            return s

        def is_zero(self):
            return self.x == 0

        def is_square(self):
            # This function works only if the modulus is odd.
            #
            # This is a Legendre/Jacobi symbol, that follows the same
            # reduction steps as a binary GCD.
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported division: even modulus')
            a = self.x
            b = m
            if a == 0:
                return True
            ls = 1
            while a != 0:
                if (a & 1) == 0:
                    a >>= 1
                    if ((b + 2) & 7) > 4:
                        ls = -ls
                else:
                    if a < b:
                        a, b = b, a
                        if (a & b & 3) == 3:
                            ls = -ls
                    a -= b
            return ls == 1

        def is_negative(self):
            """
            Test whether this value is "negative". A field element is
            formally declared negative if its representation as an
            integer in the 0 to m-1 range (with m being the field
            modulus) is an odd integer.
            """
            return (self.x & 1) != 0

# =========================================================================
# Concrete fields:
#
#   GF255e       field for jq255e point coordinates; modulus m = 2^255 - 18651
#
#   Scalar255e   field for integers modulo the jq255e group prime order:
#                r = 2^254 - 131528281291764213006042413802501683931
#
#   GF255s       field for jq255s point coordinates; modulus m = 2^255 - 3957
#
#   Scalar255s   field for integers modulo the jq255s group prime order:
#                r = 2^254 + 56904135270672826811114353017034461895

GF255e = Zmod(2**255 - 18651)
Scalar255e = Zmod(2**254 - 131528281291764213006042413802501683931)
GF255s = Zmod(2**255 - 3957)
Scalar255s = Zmod(2**254 + 56904135270672826811114353017034461895)

# =========================================================================
# Curves and points:
#
# An instance of Jq255Curve represents one of the curves, or, more
# accurately, the prime order group defined out of the curve. Group
# elements ('points') are points on the curve that are part of that
# subgroup. Each point instance is immutable. A new point instance is
# obtained by calling an appropriate method on the Jq255Curve instance,
# or by using the functions and operators on existing points.

class Jq255Curve:
    def __init__(self, name):
        if name == 'jq255e' or name == 'Jq255e':
            name = 'Jq255e'
            self.bname = b'jq255e'
            self.K = GF255e
            self.SF = Scalar255e
            self.a = self.K(0)
            self.b = self.K(-2)
            self.eta = self.K(-1).sqrt()
            Gx = self.K(2)
            Gu = self.K(1)
        elif name == 'jq255s' or name == 'Jq255s':
            name = 'Jq255s'
            self.bname = b'jq255s'
            self.K = GF255s
            self.SF = Scalar255s
            self.a = self.K(-1)
            self.b = self.K(1)/2
            self.nonQR = self.K(-1)
            Gx = self.K(26116555989003923291153849381583511726884321626891190016751861153053671511729)
            Gu = self.K(3)
        else:
            raise Exception('Unknown curve: {0}'.format(name))
        self.name = name
        self.ap = -2*self.a
        self.bp = self.a**2 - 4*self.b
        self.encodedLen = self.K.encodedLen
        self.N = Jq255Curve.Point(self, self.K.minus_one, self.K.one, self.K.zero, self.K.zero)
        GZ = Gx**2 + self.a*Gx + self.b
        self.G = Jq255Curve.Point(self, Gx**2 - self.b, GZ, Gu*GZ, (Gu**2)*GZ)

    def __call__(self, e, u):
        e = self.K(e)
        u = self.K(u)
        if e**2 != self.bp*u**4 + self.ap*u**2 + self.K.one:
            raise Exception('Invalid coordinates')
        return Jq255Curve.Point(self, e, self.K.one, u, u**2)

    def Decode(self, bb):
        """
        Decode 32 bytes (bb) into a point. This function enforces canonical
        representation.
        """
        u = self.K.Decode(bb)
        t = u**2
        d = self.bp*(t**2) + self.ap*t + self.K.one
        e = d.sqrt()
        if e is False:
            raise Exception('Invalid encoded point')
        # Test disabled: Zmod.sqrt() already returns the non-negative root
        # if e.is_negative():
        #     e = -e
        return Jq255Curve.Point(self, e, self.K.one, u, t)

    def MapToCurve(self, bb):
        """
        Map a 32-byte input (bb) to a curve point. This map is not
        surjective and not uniform, but each output point can only have
        a limited number of antecedents, so that a proper hash-to-curve
        process can be built by generating 64 bytes from a hash
        function, mapping each half to a point, and adding the two
        points together.
        """
        # Decode input into a field element.
        f = self.K.DecodeReduce(bb)

        # In order to more easily support implementations with formulas that
        # require each point to be of the form P+N with P an r-torsion point,
        # we map to a point on the dual curve y^2 = x^3 - 2*a*x + (a^2-4*b)
        # so that get a point on the curve, then apply the isogeny:
        #   (x, u) -> (4*b*u^2, 2/(u*(x-b/x)))
        # to obtain a point in the proper subset of the intended curve.
        #
        # Below, we denote aa = -2*a and bb = a^2 - 4*b. We must use
        # different methods, depending on whether a == 0 or a != 0.
        aa = self.ap
        bb = self.bp

        # The code below computes the fractional (x,u) = (X/Z, U/T)
        # coordinates of the point in the dual curve. Formulas differ
        # depending on the curve type.
        if aa.is_zero():
            # For curves with equation y^2 = x^3 + bb*x, we use the
            # following formulas, for input field element f:
            #   x1 = f + (1-bb)/(4*f)
            #   x2 = d*(f - (1-bb)/(4*f))
            # with d^2 = -1 mod p. Then at least one of x1, x2 and x1*x2
            # is a valid x coordinate for a curve point. We try them in
            # that order.
            #
            # To ensure interoperability, all implementations must use the
            # same conventions for square roots. We thus use computations
            # that correspond to what optimized code would do:
            #   yy1num = 64*f^7 + 16*(3+bb)*f^5 + 4*(3-2*bb-bb^2)*f^3 + (1-bb)^3*f
            #   yy2num = -d*(64*f^7 - 16*(3+bb)*f^5 + 4*(3-2*bb-bb^2)*f^3 - (1-bb)^3*f)
            # so that:
            #   x1^3 + bb*x1 = yy1num / (64*f^4)
            #   x2^3 + bb*x2 = yy2num / (64*f^4)
            # and the resulting point is one of:
            #     (x1, sqrt(yy1num)/(8*f^2))
            #     (x2, sqrt(yy2num)/(8*f^2))
            #     (x1*x2, sqrt(yy1num*yy2num)/(64*f^4))
            # The square root extraction (and "sign" normalization) is then
            # done on either yy1num, yy2num, or yy1num*yy2num.

            # 0 maps to N.
            if f.is_zero():
                return self.N

            d = self.eta
            x1num = 4*f**2 + (1-bb)
            x2num = d*(4*f**2 - (1-bb))
            x12den = 4*f

            yy1num = 64*f**7 + 16*(3+bb)*f**5 + 4*(3-2*bb-bb**2)*f**3 + (1-bb)**3*f
            yy2num = -d*(64*f**7 - 16*(3+bb)*f**5 + 4*(3-2*bb-bb**2)*f**3 - (1-bb)**3*f)
            y12den = 8*f**2

            if yy1num.is_square():
                xnum = x1num
                xden = x12den
                ynum = yy1num.sqrt()
                yden = y12den
            elif yy2num.is_square():
                xnum = x2num
                xden = x12den
                ynum = yy2num.sqrt()
                yden = y12den
            else:
                xnum = x1num*x2num
                xden = x12den**2
                ynum = (yy1num*yy2num).sqrt()
                yden = y12den**2

            # u = x/y
            X = xnum
            Z = xden
            U = xnum*yden
            T = xden*ynum

        else:
            # For curves y^2 = x^3 + aa*x^2 + bb*x with aa != 0, we use
            # the Elligator2 map:
            #   d = some non-square fixed value (e.g. d = -1 when p = 3 mod 4)
            #   if d*f^2 == -1:
            #       return N
            #   v = -aa/(1 + d*f^2)
            #   ls = Legendre(v*(v^2 + aa*v + bb))
            #   if ls == 1:
            #       x = v
            #   else:
            #       x = -v - aa
            #   y = ls*sqrt(x*(x^2 + aa*x + bb))
            #
            # To ensure interoperability, all implementations must use the
            # same conventions for square roots. We thus use computations
            # that correspond to what optimized code would do:
            #   yy1num = -aa*bb*d^3*f^6 + (aa^3-3*aa*bb)*d^2*f^4
            #            + (aa^3-3*aa*bb)*d*f^2 - aa*bb
            #   yy2num = -aa*bb*d^4*f^8 + (aa^3-3*aa*bb)*d^3*f^6
            #            + (aa^3-3*aa*bb)*d^2*f^4 - aa*bb*d*f^2
            #          = yy1num*d*f^2
            #   y12den = (1 + d*f^2)^4
            # If yy1num is a square, we use it; otherwise, we use yy2num.
            # The square root ynum is extracted and normalized (least
            # significant bit is set to zero); for the denominator,
            # we use: yden = (1 + d*f^2)^2

            d = self.nonQR
            Z = 1 + d*f**2
            if Z.is_zero():
                return self.N
            yy1num = -aa*bb*d**3*f**6 + (aa**3-3*aa*bb)*d**2*f**4 + (aa**3-3*aa*bb)*d*f**2 - aa*bb
            yy2num = yy1num*d*f**2
            if yy1num.is_square():
                X = -aa
                ynum = yy1num.sqrt()
            else:
                X = -aa*d*f**2
                ynum = -yy2num.sqrt()
            yden = Z**2

            # If f == 0, then we may get ynum == 0 here. In that case,
            # the point is N and we return it. Otherwise, the point is
            # not the neutral, and the subsequent computations won't fail.
            if ynum.is_zero():
                return self.N

            # u = x/y
            U = X*yden
            T = Z*ynum

        # Apply the isogeny:
        #   x' = 4*b*u^2
        #   u' = 2*x/(u*(x^2 - bb))
        xnum = 4*self.b*U**2
        xden = T**2
        unum = 2*X*Z*T
        uden = U*(X**2 - bb*Z**2)

        # Compute the e coordinate:
        #   e' = (x'^2 - b)/(x'^2 + a*x + b)
        enum = xnum**2 - self.b*xden**2
        eden = xnum**2 + self.a*xnum*xden + self.b*xden**2

        # Convert to extended coordinates and return the point.
        E = enum*(uden**2)
        Z = eden*(uden**2)
        U = unum*uden*eden
        T = (unum**2)*eden
        return Jq255Curve.Point(self, E, Z, U, T)

    # Points internally use extended (E:Z:U:T) coordinates, with:
    #    e == E/Z   u == U/Z   u^2 == T/Z   Z != 0
    class Point:
        def __init__(self, curve, E, Z, U, T):
            self.curve = curve
            self.E = E
            self.Z = Z
            self.U = U
            self.T = T

        def is_neutral(self):
            return self.U.is_zero()

        def coordinatesOfOther(self, other):
            if isinstance(other, Jq255Curve.Point):
                if self.curve is other.curve:
                    return (other.E, other.Z, other.U, other.T)
            raise Exception('Curve mismatch')

        def __add__(self, other):
            E1, Z1, U1, T1 = self.E, self.Z, self.U, self.T
            E2, Z2, U2, T2 = self.coordinatesOfOther(other)
            ap = self.curve.ap
            bp = self.curve.bp
            e1e2 = E1*E2
            z1z2 = Z1*Z2
            u1u2 = U1*U2
            t1t2 = T1*T2
            tz = (Z1 + T1)*(Z2 + T2) - z1z2 - t1t2
            eu = (E1 + U1)*(E2 + U2) - e1e2 - u1u2
            hd = z1z2 - bp*t1t2
            E3 = (z1z2 + bp*t1t2)*(e1e2 + ap*u1u2) + 2*bp*u1u2*tz
            Z3 = hd**2
            T3 = eu**2
            U3 = ((hd + eu)**2 - Z3 - T3) >> 1
            return Jq255Curve.Point(self.curve, E3, Z3, U3, T3)

        def __neg__(self):
            return Jq255Curve.Point(self.curve, self.E, self.Z, -self.U, self.T)

        def __sub__(self, other):
            return self + (-other)

        def __mul__(self, n):
            # Make sure the scalar is in the proper field of scalars. This
            # ensures modular reduction if the source value is an integer.
            if isinstance(n, Zmod.Element) and (n.ring is self.curve.SF):
                n = int(n)
            else:
                n = int(self.curve.SF(n))

            # Simple double-and-add algorithm. In this implementation,
            # we aim for clarity, not performance or mitigation of side
            # channels.
            if n == 0:
                return self.curve.N
            P = self
            nlen = n.bit_length()
            for i in range(0, nlen - 1):
                j = nlen - 2 - i
                P += P
                if ((n >> j) & 1) != 0:
                    P += self
            return P

        def __rmul__(self, n):
            return self * n

        def __eq__(self, other):
            E1, Z1, U1, T1 = self.E, self.Z, self.U, self.T
            E2, Z2, U2, T2 = self.coordinatesOfOther(other)
            return U1*E2 == U2*E1

        def __ne__(self, other):
            E1, Z1, U1, T1 = self.E, self.Z, self.U, self.T
            E2, Z2, U2, T2 = self.coordinatesOfOther(other)
            return U1*E2 != U2*E1

        def eu(self):
            """
            Get the (e,u) coordinates of a point representing this
            group element. Each element has two possible representations
            as a point, exactly one of which has a non-negative quantity
            e/u^2; this function returns that exact point coordinates.
            For the neutral group element, (-1,0) is returned.
            """
            E, Z, U, T = self.E, self.Z, self.U, self.T
            if U.is_zero():
                return (self.curve.K.minus_one, self.curve.K.zero)
            k = 1/(T*Z)
            iZ = k*T
            iT = k*Z
            e = E*iZ
            u = U*iZ
            if (E*iT).is_negative():
                e, u = -e, -u
            return (e, u)

        def xy(self):
            """
            Get the (x,y) coordinates of a point representing this
            group element. Each element has two possible representations
            as a point, exactly one of which has a non-negative quantity
            e/u^2; this function returns that exact point coordinates.
            For the neutral group element, (0,0) is returned.
            """
            E, Z, U, T = self.E, self.Z, self.U, self.T
            if U.is_zero():
                return (self.curve.K.zero, self.curve.K.zero)
            k = 1/(2*U*T)
            iT = 2*U*k
            if (E*iT).is_negative():
                E, U, k = -E, -U, -k
            m = (E + Z - self.curve.a*T)*k
            x = m*U
            y = m*Z
            return (x, y)

        def ww(self):
            """
            Get the square of the w = 1/u coordinate for this element. Note
            that the two possible representative points for this element lead
            to the same output. If this element is the neutral, then zero
            is returned.
            """
            # Division by zero in Zmod returns 0, which is what we want
            # in that case.
            return self.Z / self.T

        def __getattr__(self, name):
            if name == 'x':
                x, y = self.xy()
                return x
            elif name == 'y':
                x, y = self.xy()
                return y
            elif name == 'e':
                e, u = self.eu()
                return e
            elif name == 'u':
                e, u = self.eu()
                return u
            raise AttributeError()

        def __repr__(self):
            e, u = self.eu()
            return '{0}({1}, {2})'.format(self.curve.name, e, u)

        def __bytes__(self):
            iZ = 1 / self.Z
            u = self.U * iZ
            if (self.E * iZ).is_negative():
                u = -u
            return bytes(u)

# =========================================================================
# Concrete curves:
#
#   Jq255e    equation y^2 = x*(x^2 - 2) in field GF(2^255-18651)
#                      e^2 = 8*u^4 + 1
#
#   Jq255s    equation y^2 = x*(x^2 - x + 1/2) in field GF(2^255-3957)
#                      e^2 = -u^4 + 2*u^2 + 1

Jq255e = Jq255Curve('jq255e')
Jq255s = Jq255Curve('jq255s')

# =========================================================================
# High-level cryptographic algorithms.
#
# We define key exchange (ECDH) and signatures (Schnorr) on top of
# both jq255e and jq255s.
#
# Noteworthy details:
#
#  - A private key is an integer in the 1..r-1 range. A private key is
#    encoded over 32 bytes. When decoding, all bits are taken into
#    account (no ignored bit). Out-of-range values are rejected when
#    decoding. Note that 0 is not a valid private key.
#
#  - A public key is a point. It encodes into 32 bytes. When decoding, all
#    bits are taken into account (no ignored bit). Canonical encoding is
#    enforced: a given curve point can be validly encoded in only one way.
#    The group neutral (N, encoded as a sequence of bytes of value 0x00)
#    is not a valid public key; such a value MUST be rejected if
#    encountered when decoding.
#
#  - An ECDH message is a public key. It follows the rules of public keys,
#    as stated above. Thus, it cannot be a neutral point.
#
#  - A signature is the concatenation of a challenge value (16 bytes)
#    and a scalar (32 bytes). The scalar follows the same rules as the
#    private key, except that the value 0 is valid. The challenge is
#    interpreted as an integer in the 0 to 2^128-1 range, using the
#    unsigned little-endian encoding convention. Out of range values for
#    the scalar MUST still be rejected, and there is no ignored bit.
#
#  - Since the group has prime order, there is no ambiguousness about
#    the signature verification equation.

import hashlib
import os

def Keygen(curve, sh = None):
    """
    Generate a new keypair. If sh is provided, then it must be an object
    that implements a function digest(len), that outputs 'len' bytes,
    and can be invoked repeatedly if needed to get more bytes. An
    instance of SHAKE128 or SHAKE256, already loaded with a random seed,
    is appropriate. If sh is not provided (or is None), then the
    OS-provided random generator (os.urandom()) is used.

    Returned value is the private key (as a scalar instance).
    """
    if sh == None:
        sh = hashlib.shake_256()
        sh.update(os.urandom(32))
    j = 0
    while True:
        # We use a loop on the off-chance that we get a value which is
        # zero modulo r. This is extremely improbable and nobody knows
        # how to initialize a SHAKE256 context so that it outputs such
        # a value.
        #
        # We only extract 32 bytes (256 bits) at a time, because the
        # group order (on both jq255e and jq255s) is close enough to
        # 2^254 that the modulo reduction induces no statistically
        # detectable bias.
        bb = sh.digest(curve.encodedLen * (j + 1))
        sk = curve.SF.DecodeReduce(bb[curve.encodedLen * j:])
        if not sk.is_zero():
            return sk
        j += 1

def EncodePrivate(sk):
    """
    Encode a private key into bytes (exactly 32 bytes for both
    jq255e and jq255s).
    """
    return bytes(sk)

def DecodePrivate(curve, bb):
    """
    Decode a private key from bytes. Note that the length must match the
    expected value (32 bytes for both jq255e and jq255s) and the value
    is verified to be in the proper range (1 to r-1, with r being the
    prime order of the jq255* group).
    """
    sk = curve.SF.Decode(bb)
    if sk.is_zero():
        raise Exception('Invalid private key (zero)')
    return sk

def MakePublic(curve, sk):
    """
    Make a public key (curve point) out of a private key.
    """
    return curve.G * sk

def EncodePublic(pk):
    """
    Encode a public key into bytes.
    """
    return bytes(pk)

def DecodePublic(curve, bb):
    """
    Decode a public key from bytes. Invalid points are rejected. The
    neutral element is NOT accepted as a public key.
    """
    pk = curve.Decode(bb)
    if pk.is_neutral():
        raise Exception('Invalid public key (neutral point)')
    return pk

def ECDH(sk, pk, peer_pk, secret_len = 0, sh = None):
    """
    Do an ECDH key exchange. sk is our private key; pk is the matching
    public key (normally generated from sk with makePublic()). peer_pk
    is the public key received from the peer.

    secret_len is the length, in bytes, of the shared secret to
    generate; sh is the hash object that is used to process the internal
    ECDH output into the shared secret. If sh is not provided (or is
    None), then BLAKE2s is used. If secret_len is not provided or has
    value zero, then the natural output size of the digest function 'sh'
    is used (with its 'digest_size' field); if sh.digest_size is zero
    (e.g. because sh is a SHAKE instance, which has a variable output
    size), then secret_len is implicitly set to 32. If the requested
    output size exceeds the actual output size of the hash function,
    then an exception is raised. If the requested output size is lower
    than the output size of the hash function, then the hash output is
    truncated to that length.

    peer_pk may be either a decoded point (from decodePublic()), or
    directly the received bytes (as an array of bytes or a 'bytes' object).
    If peer_pk is a decoded point, on the same curve as our public key,
    and not the neutral point, then the process cannot fail.

    If peer_pk is provided in encoded format (as bytes), then this
    function decodes it internally. Upon decoding failure, or if the
    bytes encode the neutral point, which is not a valid public key,
    then the alternate key derivation is used: the ecdh() function does
    not fail, but instead generates a secret key in a way which is
    deterministic from the exchanged public values, and our private key.
    External attackers cannot distinguish between a success or a
    failure; this is meant for some (rare) protocols in which exchanged
    points are masked, and outsiders shall not be able to find out
    whether a given sequence of bytes is the masked value of a proper
    point or not.

    Returned value are:
       (ok, key)
    with:
       ok    boolean, True for success, False for failure
       key   the generated secret, of length 'secret_len' bytes
    """
    curve = pk.curve
    enc_peer_pk = bytes(peer_pk)
    peer_pk_good = True
    if isinstance(peer_pk, Jq255Curve.Point):
        if not(pk.curve is peer_pk.curve):
            raise Exception('Curve mismatch in ECDH')
        if pk.is_neutral():
            raise Exception('Peek public key is invalid (neutral element)')
    else:
        # We are going to decode the public key bytes. In that mode,
        # failures should trigger the alternate key derivation feature,
        # instead of being reported as exceptions. This implementation
        # is not constant-time, and the exception-catching process below
        # may leak to outsider through timing-based side channels that
        # the received bytes were not a valid public key; in a
        # production-level secure implementation, this side channel
        # should be avoided as well.
        try:
            peer_pk = pk.curve.Decode(enc_peer_pk)
            if peer_pk.is_neutral():
                raise Exception('key is neutral')
        except Exception:
            peer_pk_good = False
            peer_pk = curve.G

    # The ECDH core: multiply the peer point by our private key.
    # The shared secret is the _square_ of the w coordinate of the result
    # (a square is used to make ECDH implementable with a ladder
    # algorithm that avoids full decoding of the input point).
    shared = peer_pk * sk

    # For key generation, we want to use the digest over the concatenation of:
    #   - the two public keys;
    #   - a byte of value 0x53 (on success) or 0x46 (on failure, because the
    #     provided peer key bytes are not the valid encoding of a valid
    #     public key);
    #   - the shared secret (our own private key on failure).
    # We order the public keys by interpreting them as integers
    # (big-endian convention) so that both parties use the same order
    # (equivalently, the two keys are ordered lexicographically).
    if sh is None:
        sh = hashlib.blake2s()
    pk1 = bytes(pk)
    ipk1 = int.from_bytes(pk1, byteorder='big')
    pk2 = enc_peer_pk
    ipk2 = int.from_bytes(pk2, byteorder='big')
    if ipk1 > ipk2:
        pk1, pk2 = pk2, pk1
    sh.update(pk1)
    sh.update(pk2)
    if peer_pk_good:
        sh.update(b'\x53')
        sh.update(bytes(shared))
    else:
        sh.update(b'\x46')
        sh.update(bytes(sk))
    if sh.digest_size == 0:
        if secret_len == 0:
            secret_len = 32
        sec = sh.digest(secret_len)
    else:
        sec = sh.digest()
        if secret_len != 0:
            if secret_len > len(sec):
                raise Exception('digest output size is less than requested')
            if secret_len < len(sec):
                sec = sec[0:secret_len]
    return (peer_pk_good, sec)

# Defined hash function names.
HASHNAME_SHA224      = b'sha224'
HASHNAME_SHA256      = b'sha256'
HASHNAME_SHA384      = b'sha384'
HASHNAME_SHA512      = b'sha512'
HASHNAME_SHA512_224  = b'sha512224'
HASHNAME_SHA512_256  = b'sha512256'
HASHNAME_SHA3_224    = b'sha3224'
HASHNAME_SHA3_256    = b'sha3256'
HASHNAME_SHA3_384    = b'sha3384'
HASHNAME_SHA3_512    = b'sha3512'
HASHNAME_BLAKE2B     = b'blake2b'
HASHNAME_BLAKE2S     = b'blake2s'

# Normalize a hash function name:
#   An empty stirng (binary or not) is converted to None
#   A non-empty text string is encoded into UTF-8
def normalize_hash_name(hash_name):
    if hash_name is None or hash_name == '' or hash_name == b'':
        return None
    if isinstance(hash_name, str):
        hash_name = bytes(hash_name, encoding='utf-8')
    if not(isinstance(hash_name, bytes)):
        raise Exception('Invalid object type for a hash function name')
    return hash_name

# Internal function used in signature generation and verification: it
# computes the "challenge" as the hash of the concatenation of:
#   - the R point (first half of the signature);
#   - the public key (pk);
#   - the raw or hashed data, with the following format:
#       Raw data: one byte of value 0x52, followed by the data bytes
#       Hashed data: one byte of value 0x48, followed by the hash
#       function name, then a byte of value 0x00, then the hash value
#
# The hash function name can be provided as a string, which gets internally
# encoded into bytes wioth UTF-8 rules (no BOM) (an already encoded binary
# string can also be provided). In general, such names are derived from the
# "usual" function name, using lowercase and removing separator punctuation,
# as follows:
#    SHA-224       sha224
#    SHA-256       sha256
#    SHA-384       sha384
#    SHA-512       sha512
#    SHA-512/224   sha512224
#    SHA-512/256   sha512256
#    SHA3-224      sha3224
#    SHA3-256      sha3256
#    SHA3-384      sha3384
#    SHA3-512      sha3512
#    BLAKE2s       blake2s
#    BLAKE2b       blake2b
#
# If the provided 'hash_name' is None (or an empty string), then the data
# (in 'hv') is assumed to be the raw unhashed data.
#
# Computation of the challenge uses another hash function, which can be
# configured through the 'sh' object (if sh is unprovided or None, then
# BLAKE2s is used). This hash function needs not be the same as the one
# which was used to process the input data into the 'hv' value, although
# it is recommended to use BLAKE2s for both. Only the first 16 bytes of
# the output of 'sh' are used; however, the hash function MUST have an
# "internal pipe width" of at least 256 bits (i.e. sh should be a hash
# function that naturally outputs at least 256 bits).
#
# A variable-length hash function (XOF) such as SHAKE256 can also be
# used for 'sh'.
def make_challenge(R, pk, hash_name, hv, sh = None):
    hash_name = normalize_hash_name(hash_name)
    if sh is None:
        sh = hashlib.blake2s()
    sh.update(bytes(R))
    sh.update(bytes(pk))
    if hash_name is None:
        sh.update(b'\x52')
    else:
        sh.update(b'\x48')
        sh.update(hash_name)
        sh.update(b'\x00')
    sh.update(hv)
    if sh.digest_size == 0:
        c = sh.digest(16)
    else:
        c = sh.digest()
        if len(c) < 16:
            raise Exception('Hash output size is too low')
        if len(c) > 16:
            c = c[0:16]
    return c

def Sign(sk, pk, hash_name, hv, seed = b''):
    """
    Sign the provided (hashed) data 'hv'. The signer's private (sk) and
    public (pk) keys are used. The data is assumed to have been hashed
    with the hash function identified by 'hash_name' (hash function names
    are lowercase and use no punctuation, e.g. 'sha256' for SHA-256);
    if the input data provided as 'hv' is the raw unhashed data, then
    'hash_name' should be None or an empty string. Binary strings can also
    be used as hash function names.

    Using raw data makes the signature engine resilient to collision
    attacks on hash functions, but it also makes streamed processing
    harder for memory-constrained systems. Using a collision-resistant
    hash function (e.g. BLAKE2s or SHA3-256) is recommended.

    The 'seed' is an optional binary string that can augment the internal
    generation of the per-secret signature. Without a seed, deterministic
    generation is used, which is safe. An extra non-constant seed value
    (which needs not be random) makes signatures randomized; it can also
    provide some extra resilience against fault attacks (of course, if
    fault attacks are an issue, then side channels are also an issue,
    and this reference implementation shall not be used since it is not
    resistant to side channels).
    """
    curve = pk.curve
    hash_name = normalize_hash_name(hash_name)

    # Make the per-signature k value. We use BLAKE2s over a concatenation
    # of our private key, our public key, the provided seed, and the
    # data itself (with the hash function name, if applicable). The
    # output is interpreted as an integer, and reduced modulo r. Since
    # r is very close to a power of 2 for both jq255e and jq255s
    # (in both cases, r = 2^254 + r0 for some r0 such that |r0| < 2^127),
    # the modular reduction induces only a negligible bias.
    sh = hashlib.blake2s()
    sh.update(bytes(sk))
    sh.update(bytes(pk))
    sh.update(len(seed).to_bytes(8, 'little'))
    sh.update(seed)
    if hash_name is None:
        sh.update(b'\x52')
    else:
        sh.update(b'\x48')
        sh.update(hash_name)
        sh.update(b'\x00')
    sh.update(hv)
    k = curve.SF.DecodeReduce(sh.digest())

    # Use the per-signature secret scalar k to generate the signature.
    R = curve.G * k
    cb = make_challenge(R, pk, hash_name, hv)
    c = int.from_bytes(cb, byteorder='little')
    s = k + c*sk
    return cb + bytes(s)

def Verify(pk, sig, hash_name, hv):
    """
    Verify the signature 'sig' (bytes) over the provided (hashed) data
    'hv' (hashed with the function identified by 'hash_name'; use None or
    the empty string b'' if data is unhashed) against the public key pk.
    Returned value is True on success (signature is valid for this
    public key and that data), False otherwise.
    """
    try:
        curve = pk.curve
        if len(sig) != 48:
            return False
        cb = sig[0:16]
        c = int.from_bytes(cb, byteorder='little')
        s = curve.SF.Decode(sig[16:])
        R = curve.G*s - pk*c
        cb2 = make_challenge(R, pk, hash_name, hv)
        return cb == cb2
    except Exception:
        return False

def HashToCurve(curve, hash_name, hv):
    """
    Hash the provided input data into a curve point. The data (hv) is
    either raw unhashed data, or a hash value if the data was pre-hashed.
    'hash_name' identifies the hash function used for pre-hashing; use None
    or b'' (empty string) for raw unhashed data. Returned point can be any
    point on the group, including the neutral N.
    """
    hash_name = normalize_hash_name(hash_name)
    if hash_name is None:
        sh = hashlib.blake2s()
        sh.update(b'\x01')
        sh.update(b'\x52')
        sh.update(hv)
        blob1 = sh.digest()
        sh = hashlib.blake2s()
        sh.update(b'\x02')
        sh.update(b'\x52')
        sh.update(hv)
        blob2 = sh.digest()
    else:
        sh = hashlib.blake2s()
        sh.update(b'\x01')
        sh.update(b'\x48')
        sh.update(hash_name)
        sh.update(b'\x00')
        sh.update(hv)
        blob1 = sh.digest()
        sh = hashlib.blake2s()
        sh.update(b'\x02')
        sh.update(b'\x48')
        sh.update(hash_name)
        sh.update(b'\x00')
        sh.update(hv)
        blob2 = sh.digest()

    return curve.MapToCurve(blob1) + curve.MapToCurve(blob2)
