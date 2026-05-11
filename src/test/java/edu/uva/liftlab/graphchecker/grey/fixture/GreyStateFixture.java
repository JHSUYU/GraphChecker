package edu.uva.liftlab.graphchecker.grey.fixture;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class GreyStateFixture {
    private final Map<Integer, BlockKey> allKeys = new HashMap<Integer, BlockKey>();
    private BlockKey currentKey = new BlockKey(1, 10);
    private DataEncryptionKey encryptionKey;

    public byte[] retrieveDataEncryptionKey(int keyId, byte[] nonce) throws InvalidEncryptionKeyException {
        BlockKey key = allKeys.get(keyId);
        if (key == null) {
            throw new InvalidEncryptionKeyException();
        }
        return nonce;
    }

    public DataEncryptionKey newDataEncryptionKey() {
        if (encryptionKey == null) {
            encryptionKey = generateDataEncryptionKey();
        }
        return encryptionKey;
    }

    public DataEncryptionKey generateDataEncryptionKey() {
        BlockKey key = currentKey;
        return new DataEncryptionKey(key.getKeyId(), Time.now() + 10);
    }

    public void addKeys(ExportedKeys exportedKeys) {
        allKeys.put(exportedKeys.key.getKeyId(), exportedKeys.key);
    }

    public void removeExpiredKeys() {
        long now = Time.now();
        for (Iterator<BlockKey> iterator = allKeys.values().iterator(); iterator.hasNext();) {
            BlockKey key = iterator.next();
            if (key.getExpiryDate() < now) {
                iterator.remove();
            }
        }
    }

    public String getUserNameFromEncryptionKey(DataEncryptionKey key) {
        return key.keyId + ":" + key.expiryDate;
    }

    public byte[] getEncryptionKeyFromUserName(String userName) throws InvalidEncryptionKeyException {
        String[] pieces = userName.split(":");
        int keyId = Integer.parseInt(pieces[0]);
        return retrieveDataEncryptionKey(keyId, new byte[0]);
    }

    public void run() throws InterruptedException {
        while (true) {
            addKeys(new ExportedKeys(new BlockKey(2, Time.now() + 10)));
            Thread.sleep(1);
        }
    }

    public void recoverWithoutRepair(Exception exception) {
        System.err.println(exception.getMessage());
        setHasFailure();
        activateDelay();
    }

    public void dispatchWithCatch(int keyId) {
        try {
            retrieveDataEncryptionKey(keyId, new byte[0]);
        } catch (InvalidEncryptionKeyException exception) {
            System.err.println(exception.getMessage());
            setHasFailure();
            activateDelay();
        }
    }

    private void setHasFailure() {
    }

    private void activateDelay() {
    }

    public static final class BlockKey {
        private final int keyId;
        private final long expiryDate;

        public BlockKey(int keyId, long expiryDate) {
            this.keyId = keyId;
            this.expiryDate = expiryDate;
        }

        public int getKeyId() {
            return keyId;
        }

        public long getExpiryDate() {
            return expiryDate;
        }
    }

    public static final class DataEncryptionKey {
        public final int keyId;
        public final long expiryDate;

        public DataEncryptionKey(int keyId, long expiryDate) {
            this.keyId = keyId;
            this.expiryDate = expiryDate;
        }
    }

    public static final class ExportedKeys {
        private final BlockKey key;

        public ExportedKeys(BlockKey key) {
            this.key = key;
        }
    }

    public static final class Time {
        public static long now() {
            return System.currentTimeMillis();
        }
    }

    public static final class InvalidEncryptionKeyException extends Exception {
    }
}
