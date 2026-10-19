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

public final class ReplayKeys extends Provider {
    private static final long serialVersionUID = 1L;
    private static final String NAME = "CausynthReplayKeys";
    private static final String POOL = "replay-rsa-keys.txt";
    private static final Set<Integer> NAMED =
            ConcurrentHashMap.<Integer>newKeySet();

    private ReplayKeys() {
        super(NAME, 1.0, "the RSA key pairs of a concolic replay, from a pool");
        put("KeyPairGenerator.RSA", Rsa.class.getName());
    }

    static void install() {
        if (Security.getProvider(NAME) == null) {
            Security.insertProviderAt(new ReplayKeys(), 1);
        }
    }

    public static final class Rsa extends KeyPairGeneratorSpi {
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
