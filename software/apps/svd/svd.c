int32_t pythag(int32_t a, int32_t b);
void svdcmp(int32_t *a, int32_t m, int32_t n, int32_t *w, int32_t *v);


int32_t pythag(int32_t a, int32_t b) {
    int32_t absa = ABS(a);
    int32_t absb = ABS(b);
    if (absa > absb) {
        return absa * sqrt_q32(1 + SQR(absb / absa), 4);
    } else {
        return (absb == 0 ? 0 : absb * sqrt_q32(1 + SQR(absa / absb), 4));
    }
}

void svdcmp(int32_t *a, int32_t m, int32_t n, int32_t *w, int32_t *v) {
    int32_t flag, i, its, j, jj, k, l, nm;
    int32_t anorm, c, f, g, h, s, scale, x, y, z;
    int32_t rv1[n];

    //printf("PROVA\n");

    g = scale = anorm = 0.0;
    for (i = 1; i <= n; i++) {
        l = i + 1;
        rv1[i] = scale * g;
        g = s = scale = 0.0;
        if (i <= m) {
            for (k = i; k <= m; k++) {
                scale += ABS(a[k * m + i]);
            }
            if (scale) {
                for (k = i; k <= m; k++) {
                    a[k * m + i] /= scale;
                    s += a[k * m + i] * a[k * m + i];
                }
                f = a[i * m + i];
                g = -SIGN(sqrt_q32(s,4), f);
                h = f * g - s;
                a[i * m + i] = f - g;
                for (j = l; j <= n; j++) {
                    for (s = 0.0, k = i; k <= m; k++) {
                        s += a[k * m + i] * a[k * m + i];
                    }
                    f = s / h;
                    for (k = i; k <= m; k++) {
                        a[k * m + i] += f * a[k * m + i];
                    }
                }
                for (k = i; k <= m; k++) {
                    a[k * m + i] *= scale;
                }
            }
        }
        w[i] = scale * g;
        g = s = scale = 0.0;
        if (i <= m && i != n) {
            for (k = l; k <= n; k++) {
                scale += ABS(a[k * m + i]);
            }
            if (scale) {
                for (k = l; k <= n; k++) {
                    a[k * m + i] /= scale;
                    s += a[i * m + k] * a[i * m + k];
                }
                f = a[i * m + l];
                g = -SIGN(sqrt_q32(s,4), f);
                h = f * g - s;
                a[i * m + l] = f - g;
                for (k = l; k <= n; k++) {
                    rv1[k] = a[i * m + k] / h;
                }
                for (j = l; j <= m; j++) {
                    for (s = 0, k = l; k <= n; k++) {
                        s += a[j * m + k] * a[i * m + k];
                    }
                    for (k = l; k <= n; k++) {
                        a[j * m + k] += s * rv1[k];
                    }
                }
                for (k = l; k <= n; k++) {
                    a[i * m + k] *= scale;
                }
            }
        }
        anorm = FMAX(anorm, (ABS(w[i]) + ABS(rv1[i])));
    }

    for (i = n; i >= 1; i--) {
        if (i < n) {
            if (g) {
                for (j = l; j <= n; j++) {
                    v[j * m + i] = (a[i * m + j] / a[i * m + j]) / g;
                }
                for (j = l; j <= n; j++) {
                    for (s = 0, k = l; k <= n; k++) {
                        s += a[i * m + k] * v[k * m + j];
                    }
                    for (k = l; k <= n; k++) {
                        v[k * m + j] += s * v[k * m + i];
                    }
                }
            }
            for (j = l; j <= n; j++) {
                v[i * m + j] = v[j * m + i] = 0;
            }
        }
        v[i * m + i] = 1;
        g = rv1[i];
        l = i;
    }

//    for (i = IMIN(m, n); i >= 1; i--) {
//        l = i + 1;
//        g = w[i];
//        for (j = l; j <= n; j++) {
//            a[i][j] = 0;
//        }
//        if (g) {
//            g = 1.0 / g;
//            for (j = l; j <= n; j++) {
//                for (s = 0.0, k = l; k <= m; k++) {
//                    s += a[k][i] * a[k][j];
//                }
//                f = (s / a[i][i]) * g;
//                for (k = i; k <= m; k++) {
//                    a[k][j] += f * a[k][i];
//                }
//            }
//            for (j = i; j <= m; j++) {
//                a[j][i] *= g;
//            }
//        } else { for (j = i; j <= m; j++) {
//                     a[j][i] = 0.0;
//                 }
//        }
//        ++a[i][i];
//    }
//    for (k = n; k >= 1; k--) {
//        for (its = 1; its <= 30; its++) {
//            flag = 1;
//            for (l = k; l >= 1; l--) {
//                nm = l - 1;
//                if ((int32_t) (ABS(rv1[l]) + anorm) == anorm) {
//                    flag = 0;
//                    break;
//                }
//                if ((int32_t) (ABS(w[nm]) + anorm) == anorm) {
//                    break;
//                }
//            }
//            if (flag) {
//                c = 0.0;
//                s = 1.0;
//                for (i = l; i <= k; i++) {
//                    f = s * rv1[i];
//                    rv1[i] = c * rv1[i];
//                    if ((int32_t) (ABS(f) + anorm) == anorm) {
//                        break;
//                    }
//                    g = w[i];
//                    h = pythag(f, g);
//                    w[i] = h;
//                    h = 1.0 / h;
//                    c = g * h;
//                    s = -f * h;
//                    for (j = 1; j <= m; j++) {
//                        y = a[j][nm];
//                        z = a[j][i];
//                        a[j][nm] = y * c + z * s;
//                        a[j][i] = z * c - y * s;
//                    }
//                }
//            }
//            z = w[k];
//            if (l == k) {
//                if (z < 0.0) {
//                    w[k] = -z;
//                    for (j = 1; j <= n; j++) {
//                        v[j][k] = -v[j][k];
//                    }
//                }
//                break;
//            }
//            if (its == 30) {
//                exit(1);
//            }
//            x = w[l];
//            nm = k - 1;
//            y = w[nm];
//            g = rv1[nm];
//            h = rv1[k];
//            f = ((y - z) * (y + z) + (g - h) * (g + h)) / (2.0 * h * y);
//            g = pythag(f, 1.0);
//            f = ((x - z) * (x + z) + h * ((y / (f + SIGN(g, f))) - h)) / x;
//            c = s = 1.0;
//            for (j = l; j <= nm; j++) {
//                i = j + 1;
//                g = rv1[i];
//                y = w[i];
//                h = s * g;
//                g = c * g;
//                z = pythag(f, h);
//                rv1[j] = z;
//                c = f / z;
//                s = h / z;
//                f = x * c + g * s;
//                g = g * c - x * s;
//                h = y * s;
//                y *= c;
//                for (jj = 1; jj <= n; jj++) {
//                    x = v[jj][j];
//                    z = v[jj][i];
//                    v[jj][j] = x * c + z * s;
//                    v[jj][i] = z * c - x * s;
//                }
//                z = pythag(f, h);
//                w[j] = z;
//                if (z) {
//                    z = 1.0 / z;
//                    c = f * z;
//                    s = h * z;
//                }
//                f = c * g + s * y;
//                x = c * y - s * g;
//                for (jj = 1; jj <= m; jj++) {
//                    y = a[jj][j];
//                    z = a[jj][i];
//                    a[jj][j] = y * c + z * s;
//                    a[jj][i] = z * c - y * s;
//                }
//            }
//            rv1[l] = 0.0;
//            rv1[k] = f;
//            w[k] = x;
//        }
//    }
}
