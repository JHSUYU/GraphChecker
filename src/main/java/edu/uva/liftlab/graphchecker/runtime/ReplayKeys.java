package edu.uva.liftlab.graphchecker.runtime;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.GeneralSecurityException;
import java.security.InvalidAlgorithmParameterException;
import java.security.KeyFactory;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.KeyPairGeneratorSpi;
import java.security.Provider;
import java.security.SecureRandom;
import java.security.Security;
import java.security.interfaces.RSAPrivateCrtKey;
import java.security.spec.AlgorithmParameterSpec;
import java.security.spec.PKCS8EncodedKeySpec;
import java.security.spec.RSAKeyGenParameterSpec;
import java.security.spec.RSAPublicKeySpec;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * The RSA key pairs of a concolic replay, from a pool instead of a prime
 * search.
 *
 * <p>The concolic VM interprets {@code java.math.BigInteger} with none of
 * HotSpot's intrinsics: one 2048-bit RSA key pair takes it 40-70 s, the stock
 * JDK 0.1-0.3 s.  A Solr node draws one as it starts ({@code CoreContainer}'s
 * {@code PublicKeyHandler}, {@code CryptoKeys.RSAKeyPair}): four nodes spent
 * 220 s of a 470 s seed replay in the search (solr-adhoc
 * OverseerCollectionMessageHandler-679, a jstack every 3 s), and every
 * obligation's replay of that workload spent it again.  A key pair is a draw
 * of {@code SecureRandom} bits no stage reads -- no root, row or symbol is
 * made of it -- so a replay JVM draws its RSA key pairs from a fixed pool,
 * pairs of public exponent 65537 generated once on the stock JDK ({@link
 * #POOL}: four per size of 1024, 2048, 3072 and 4096 bits), one after another
 * per size and the first again after the last: two pairs drawn in a row
 * differ, as two searches' would, and every replay draws the same ones.  A
 * size or exponent the pool has no pair of is the JDK's own search; either
 * way the replay log names it once per size.  The recording, on the stock
 * JDK, searches as it always does.</p>
 */
public final class ReplayKeys extends Provider {
    private static final long serialVersionUID = 1L;
    private static final String NAME = "CausynthReplayKeys";
    /** "{@code <bits> <base64 PKCS#8 RSA private CRT key>}" per line. */
    private static final String POOL = "replay-rsa-keys.txt";
    /** The sizes the replay log has named. */
    private static final Set<Integer> NAMED =
            ConcurrentHashMap.<Integer>newKeySet();

    private ReplayKeys() {
        super(NAME, 1.0, "the RSA key pairs of a concolic replay, from a pool");
        put("KeyPairGenerator.RSA", Rsa.class.getName());
    }

    /** Puts this provider first, once per replay JVM, before the workload. */
    static void install() {
        if (Security.getProvider(NAME) == null) {
            Security.insertProviderAt(new ReplayKeys(), 1);
        }
    }

    /** The RSA generator: the JDK's, with its pair drawn from the pool. */
    public static final class Rsa extends KeyPairGeneratorSpi {
        /** The JDK's own: it checks every parameter as it always does. */
        private final KeyPairGenerator jdk;
        private int bits = 2048;
        private BigInteger exponent = RSAKeyGenParameterSpec.F4;

        public Rsa() throws GeneralSecurityException {
            jdk = KeyPairGenerator.getInstance("RSA", "SunRsaSign");
        }

        @Override
        public void initialize(int keysize, SecureRandom random) {
            jdk.initialize(keysize, random);
            bits = keysize;
            exponent = RSAKeyGenParameterSpec.F4;
        }

        @Override
        public void initialize(AlgorithmParameterSpec params,
                               SecureRandom random)
                throws InvalidAlgorithmParameterException {
            jdk.initialize(params, random);
            RSAKeyGenParameterSpec rsa = (RSAKeyGenParameterSpec) params;
            bits = rsa.getKeysize();
            exponent = rsa.getPublicExponent();
        }

        @Override
        public KeyPair generateKeyPair() {
            List<KeyPair> pairs = exponent.equals(RSAKeyGenParameterSpec.F4)
                    ? Pool.PAIRS.get(bits) : null;
            if (NAMED.add(bits)) {
                EngineConsole.println("Causynth: this replay's " + bits
                        + "-bit RSA key pairs " + (pairs == null
                        ? "are the JDK's own search: the pool has none"
                        : "come from its pool of " + pairs.size()));
            }
            if (pairs == null) return jdk.generateKeyPair();
            return pairs.get(Pool.DRAWN.computeIfAbsent(bits,
                    ignored -> new AtomicInteger()).getAndIncrement()
                    % pairs.size());
        }
    }

    /** The pool, read on the first draw, with this layer's observation
     *  paused: no workload path holds its decoding. */
    private static final class Pool {
        static final Map<Integer, List<KeyPair>> PAIRS = read();
        static final Map<Integer, AtomicInteger> DRAWN =
                new ConcurrentHashMap<Integer, AtomicInteger>();

        private static Map<Integer, List<KeyPair>> read() {
            ConcolicRegionRuntime.pauseObservation();
            try (InputStream in = ReplayKeys.class.getResourceAsStream(POOL);
                 BufferedReader lines = new BufferedReader(
                         new InputStreamReader(in, StandardCharsets.UTF_8))) {
                KeyFactory rsa = KeyFactory.getInstance("RSA", "SunRsaSign");
                Map<Integer, List<KeyPair>> pairs =
                        new HashMap<Integer, List<KeyPair>>();
                for (String line; (line = lines.readLine()) != null; ) {
                    String[] row = line.trim().split(" ");
                    RSAPrivateCrtKey key = (RSAPrivateCrtKey) rsa.generatePrivate(
                            new PKCS8EncodedKeySpec(
                                    Base64.getDecoder().decode(row[1])));
                    pairs.computeIfAbsent(Integer.valueOf(row[0]),
                            ignored -> new ArrayList<KeyPair>()).add(
                            new KeyPair(rsa.generatePublic(new RSAPublicKeySpec(
                                    key.getModulus(), key.getPublicExponent())),
                                    key));
                }
                return Collections.unmodifiableMap(pairs);
            } catch (IOException | GeneralSecurityException | RuntimeException
                    unreadable) {
                throw new IllegalStateException("the replay's RSA key pool "
                        + POOL + " is unreadable", unreadable);
            } finally {
                ConcolicRegionRuntime.resumeObservation();
            }
        }
    }
}
