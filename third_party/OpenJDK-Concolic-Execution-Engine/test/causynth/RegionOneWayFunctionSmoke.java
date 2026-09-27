import java.security.MessageDigest;
import javax.crypto.Cipher;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;

/** Proves that a digest and a cipher over symbolic bytes add no constraint
 *  and hand back concrete bytes, while the caller stays concolic. */
public final class RegionOneWayFunctionSmoke {
    private static final class Input {
        int value = 7;
    }

    private static volatile int sink;

    public static void main(String[] args) throws Exception {
        MessageDigest md5 = MessageDigest.getInstance("MD5");
        Cipher cipher = Cipher.getInstance("AES/CBC/NoPadding");
        Input input = new Input();
        require(System.startConcolicRegion("REGION.one-way-function",
                "TASK.one-way-function") == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "ONE_WAY_SOURCE");
        byte[] data = new byte[16];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) (input.value + i);
        }

        String before = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        byte[] digest = md5.digest(data);
        cipher.init(Cipher.ENCRYPT_MODE, new SecretKeySpec(digest, "AES"),
                new IvParameterSpec(new byte[16]));
        byte[] sealed = cipher.doFinal(data);
        if (sealed[3] > digest[5]) sink++;
        String after = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        require(before.equals(after),
                "a one-way function constrained the path: " + after);

        boolean decision = input.value > 0;
        String businessPath = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        System.finishConcolicRegion();
        require(decision && businessPath.contains("ONE_WAY_SOURCE"),
                "the caller lost its symbolic source: " + businessPath);
        System.out.println("CAUSYNTH_ONE_WAY_FUNCTION_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
