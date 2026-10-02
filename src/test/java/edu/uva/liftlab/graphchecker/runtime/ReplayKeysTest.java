package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;

import java.math.BigInteger;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.Security;
import java.security.interfaces.RSAPublicKey;
import java.security.spec.RSAKeyGenParameterSpec;
import javax.crypto.Cipher;
import org.junit.After;
import org.junit.Test;

public class ReplayKeysTest {
    @After
    public void uninstall() {
        Security.removeProvider("CausynthReplayKeys");
    }

    /**
     * Installed, the JDK's RSA generator draws the pool's pairs one after
     * another, each a working pair, the same in every JVM; a size or an
     * exponent the pool has none of is the JDK's own search.
     */
    @Test(timeout = 60000L)
    public void anRsaKeyPairIsDrawnFromThePool() throws Exception {
        ReplayKeys.install();
        ReplayKeys.install();
        assertEquals("CausynthReplayKeys", Security.getProviders()[0].getName());
        KeyPairGenerator generator = KeyPairGenerator.getInstance("RSA");
        generator.initialize(2048);
        KeyPair first = generator.generateKeyPair();
        KeyPair second = generator.generateKeyPair();
        assertNotEquals(first.getPublic(), second.getPublic());
        for (KeyPair pair : new KeyPair[] {first, second}) {
            assertEquals(2048, ((RSAPublicKey) pair.getPublic()).getModulus()
                    .bitLength());
            Cipher rsa = Cipher.getInstance("RSA/ECB/PKCS1Padding");
            rsa.init(Cipher.ENCRYPT_MODE, pair.getPrivate());
            byte[] sealed = rsa.doFinal(new byte[] {1, 2, 3});
            rsa.init(Cipher.DECRYPT_MODE, pair.getPublic());
            assertArrayEquals(new byte[] {1, 2, 3}, rsa.doFinal(sealed));
        }
        KeyPairGenerator again = KeyPairGenerator.getInstance("RSA");
        again.initialize(new RSAKeyGenParameterSpec(2048,
                RSAKeyGenParameterSpec.F4));
        // The pool's third pair, then its fourth, then its first again.
        again.generateKeyPair();
        again.generateKeyPair();
        assertEquals(first.getPublic(), again.generateKeyPair().getPublic());
        KeyPairGenerator searched = KeyPairGenerator.getInstance("RSA");
        searched.initialize(new RSAKeyGenParameterSpec(1024, BigInteger.valueOf(3)));
        assertEquals(BigInteger.valueOf(3), ((RSAPublicKey) searched
                .generateKeyPair().getPublic()).getPublicExponent());
        searched.initialize(768);
        assertFalse(first.getPublic().equals(searched.generateKeyPair()
                .getPublic()));
    }
}
