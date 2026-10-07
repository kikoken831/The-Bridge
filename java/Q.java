import java.awt.image.BufferedImage;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import javax.imageio.ImageIO;

// java Q.java <file|dir>...  -> qr/NNN.png for every .scala/.txt file, 1000-byte chunks
public class Q {
	static final int[] E = {0,7,10,15,20,26,18,20,24,30,18,20,24,26,30,22,24,28,30,28,28,28,28,30,30,26,28,30,30,30,30,30,30,30,30,30,30,30,30,30,30};
	static final int[] B = {0,1,1,1,1,1,2,2,2,2,4,4,4,4,4,6,6,6,6,7,8,8,9,9,10,12,12,12,13,14,15,16,17,18,19,19,20,21,22,24,25};
	static boolean[][] m, f;
	static int n;

	static int mul(int x, int y) {
		int z = 0;
		for (int i = 7; i >= 0; i--) z = (z << 1) ^ (z >> 7) * 0x11D ^ (y >> i & 1) * x;
		return z;
	}

	static void set(int x, int y, boolean b) {
		if (x >= 0 && y >= 0 && x < n && y < n) { m[y][x] = b; f[y][x] = true; }
	}

	static void fmt(int mask) {
		int d = 8 | mask, r = d;
		for (int i = 0; i < 10; i++) r = r << 1 ^ (r >> 9) * 0x537;
		int b = (d << 10 | r) ^ 0x5412;
		for (int i = 0; i < 15; i++) {
			boolean v = (b >> i & 1) != 0;
			if (i < 6) set(8, i, v); else if (i < 8) set(8, i + 1, v); else set(i == 8 ? 7 : 14 - i, 8, v);
			if (i < 8) set(n - 1 - i, 8, v); else set(8, n - 15 + i, v);
		}
		set(8, n - 8, true);
	}

	static void mask(int k) {
		for (int y = 0; y < n; y++) for (int x = 0; x < n; x++) {
			int[] c = {(x + y) % 2, y % 2, x % 3, (x + y) % 3, (x / 3 + y / 2) % 2, x * y % 2 + x * y % 3, (x * y % 2 + x * y % 3) % 2, ((x + y) % 2 + x * y % 3) % 2};
			if (c[k] == 0 && !f[y][x]) m[y][x] ^= true;
		}
	}

	static int pen() {
		int p = 0;
		for (int t = 0; t < 2; t++) for (int i = 0; i < n; i++) for (int j = 1, r = 1; j < n; j++) {
			if (t == 0 ? m[i][j] == m[i][j - 1] : m[j][i] == m[j - 1][i]) { if (++r == 5) p += 3; else if (r > 5) p++; } else r = 1;
		}
		for (int y = 0; y < n - 1; y++) for (int x = 0; x < n - 1; x++)
			if (m[y][x] == m[y][x + 1] && m[y][x] == m[y + 1][x] && m[y][x] == m[y + 1][x + 1]) p += 3;
		return p;
	}

	static void put(StringBuilder s, int v, int len) {
		for (int i = len - 1; i >= 0; i--) s.append(v >> i & 1);
	}

	// Byte-mode, ECC level L. mk<0 picks the best mask.
	static boolean[][] qr(byte[] d, int mk) {
		int v = 1, raw;
		for (;; v++) {
			raw = 16 * v * v + 128 * v + 64;
			if (v > 1) { int a = v / 7 + 2; raw -= (25 * a - 10) * a - 55; if (v > 6) raw -= 36; }
			raw /= 8;
			if (4 + (v < 10 ? 8 : 16) + 8 * d.length <= 8 * (raw - E[v] * B[v])) break;
			if (v == 40) throw new IllegalArgumentException("too long");
		}
		StringBuilder s = new StringBuilder();
		put(s, 4, 4); put(s, d.length, v < 10 ? 8 : 16);
		for (byte b : d) put(s, b & 255, 8);
		int cap = (raw - E[v] * B[v]) * 8;
		put(s, 0, Math.min(4, cap - s.length()));
		put(s, 0, -s.length() & 7);
		for (int p = 0xEC; s.length() < cap; p ^= 0xEC ^ 0x11) put(s, p, 8);
		int nb = B[v], el = E[v], sh = nb - raw % nb, sl = raw / nb;
		int[][] bl = new int[nb][];
		for (int i = 0, k = 0; i < nb; i++) {
			int dl = sl - el + (i < sh ? 0 : 1);
			int[] g = new int[el]; g[el - 1] = 1;
			for (int j = 0, r = 1; j < el; j++, r = mul(r, 2))
				for (int q = 0; q < el; q++) { g[q] = mul(g[q], r); if (q + 1 < el) g[q] ^= g[q + 1]; }
			int[] b = new int[sl + 1], rem = new int[el];
			for (int j = 0; j < dl; j++, k++) {
				b[j] = Integer.parseInt(s.substring(k * 8, k * 8 + 8), 2);
				int c = b[j] ^ rem[0];
				System.arraycopy(rem, 1, rem, 0, el - 1); rem[el - 1] = 0;
				for (int q = 0; q < el; q++) rem[q] ^= mul(g[q], c);
			}
			System.arraycopy(rem, 0, b, dl + (i < sh ? 1 : 0), el);
			bl[i] = b;
		}
		List<Integer> out = new ArrayList<>();
		for (int i = 0; i <= sl; i++) for (int j = 0; j < nb; j++) if (i != sl - el || j >= sh) out.add(bl[j][i]);

		n = v * 4 + 17; m = new boolean[n][n]; f = new boolean[n][n];
		for (int i = 0; i < n; i++) { set(6, i, i % 2 == 0); set(i, 6, i % 2 == 0); }
		for (int[] c : new int[][]{{3, 3}, {n - 4, 3}, {3, n - 4}})
			for (int y = -4; y <= 4; y++) for (int x = -4; x <= 4; x++) {
				int t = Math.max(Math.abs(x), Math.abs(y)); set(c[0] + x, c[1] + y, t != 2 && t != 4);
			}
		int na = v > 1 ? v / 7 + 2 : 0, st = v == 32 ? 26 : na < 2 ? 0 : (v * 4 + na * 2 + 1) / (na * 2 - 2) * 2;
		for (int i = 0; i < na; i++) for (int j = 0; j < na; j++) {
			if (i == 0 && j == 0 || i == 0 && j == na - 1 || i == na - 1 && j == 0) continue;
			int cx = i == 0 ? 6 : n - 7 - (na - 1 - i) * st, cy = j == 0 ? 6 : n - 7 - (na - 1 - j) * st;
			for (int y = -2; y <= 2; y++) for (int x = -2; x <= 2; x++) set(cx + x, cy + y, Math.max(Math.abs(x), Math.abs(y)) != 1);
		}
		fmt(0);
		if (v > 6) {
			int r = v;
			for (int i = 0; i < 12; i++) r = r << 1 ^ (r >> 11) * 0x1F25;
			for (int i = 0; i < 18; i++) {
				boolean b = ((v << 12 | r) >> i & 1) != 0;
				set(n - 11 + i % 3, i / 3, b); set(i / 3, n - 11 + i % 3, b);
			}
		}
		for (int r = n - 1, i = 0; r >= 1; r -= 2) {
			if (r == 6) r = 5;
			for (int t = 0; t < n; t++) for (int j = 0; j < 2; j++) {
				int x = r - j, y = ((r + 1) & 2) == 0 ? n - 1 - t : t;
				if (!f[y][x] && i < out.size() * 8) m[y][x] = (out.get(i >> 3) >> (7 - (i++ & 7)) & 1) != 0;
			}
		}
		if (mk < 0) {
			int bp = 1 << 30;
			for (int k = 0; k < 8; k++) {
				mask(k); fmt(k);
				int p = pen();
				if (p < bp) { bp = p; mk = k; }
				mask(k);
			}
		}
		mask(mk); fmt(mk);
		return m;
	}

	public static void main(String[] a) throws Exception {
		List<Path> fs = new ArrayList<>();
		for (String x : a) try (var w = Files.walk(Paths.get(x))) {
			w.filter(p -> p.toString().matches(".*\\.(scala|txt)")).sorted().forEach(fs::add);
		}
		new File("qr").mkdir();
		int id = 0;
		for (Path p : fs) {
			byte[] all = Files.readAllBytes(p);
			int cnt = Math.max(1, (all.length + 999) / 1000);
			for (int c = 0; c < cnt; c++) {
				ByteArrayOutputStream o = new ByteArrayOutputStream();
				o.write((p + " " + (c + 1) + "/" + cnt + "\n").getBytes());
				o.write(all, c * 1000, Math.min(1000, all.length - c * 1000));
				boolean[][] q = qr(o.toByteArray(), -1);
				BufferedImage im = new BufferedImage((n + 8) * 8, (n + 8) * 8, 1);
				for (int y = 0; y < im.getHeight(); y++) for (int x = 0; x < im.getWidth(); x++) {
					int i = y / 8 - 4, j = x / 8 - 4;
					im.setRGB(x, y, i >= 0 && j >= 0 && i < n && j < n && q[i][j] ? 0 : -1);
				}
				ImageIO.write(im, "png", new File(String.format("qr/%03d.png", id++)));
			}
		}
	}
}
