// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define WIDTH (256)
#define HEIGHT (160)
//#define WIDTH (16)
//#define HEIGHT (8)

#define PRECISION (1024)
#define PRECISION_SQRT (32)

#define VEC3_xyz(X, Y, Z) ((Vec3){.x = X, .y = Y, .z = Z})
#define VEC3_x(X) VEC3_xyz(X, X, X)
#define VEC3 VEC3_x(0)
typedef struct Vec3 {
  int x, y, z;
} Vec3;

Vec3 image[WIDTH * HEIGHT];

static inline int sqrtint(int x) {
  if (x <= 0) {
    return 0;
  } else if (x < 2) {
    return x; /* avoid div/0 */
  }
  unsigned val = (unsigned)x;
  /* starting point is relatively unimportant */
  unsigned a = PRECISION;
  unsigned b;

  b = val / a;
  a = (a + b) / 2;
  b = val / a;
  a = (a + b) / 2;
  b = val / a;
  a = (a + b) / 2;
  b = val / a;
  a = (a + b) / 2;

  return (int)a;
  // return sqrt(x);
}

static inline int powint(int x, int exp) {
  for (int i = 1; i < exp; ++i) {
    x *= x;
  }
  return x;
}

void vec_print(Vec3 v) { printf("%d, %d, %d\n", v.x, v.y, v.z); }
static inline int vec_dot_unscaled(Vec3 a, Vec3 b) {
  return (a.x * b.x) + (a.y * b.y) + (a.z * b.z);
}

static inline int vec_dot(Vec3 a, Vec3 b) {
  return (a.x * b.x) / PRECISION + (a.y * b.y) / PRECISION +
         (a.z * b.z) / PRECISION;
}

static inline int vec_length2(Vec3 v) { return vec_dot(v, v); }
static inline int vec_length(Vec3 v) { return sqrtint(vec_length2(v)); }

static inline Vec3 vec_divide(Vec3 v, int s) {
  v.x /= s;
  v.y /= s;
  v.z /= s;
  return v;
}

static inline Vec3 vec_scale(Vec3 v, int s) {
  v.x *= s;
  v.y *= s;
  v.z *= s;
  return v;
}
static inline Vec3 vec_abs(Vec3 v) {
  v.x = v.x < 0 ? -v.x : v.x;
  v.y = v.y < 0 ? -v.y : v.y;
  v.z = v.z < 0 ? -v.z : v.z;
  return v;
}

static inline Vec3 vec_add(Vec3 a, Vec3 b) {
  return (Vec3){.x = a.x + b.x, .y = a.y + b.y, .z = a.z + b.z};
}
static inline Vec3 vec_subtract(Vec3 a, Vec3 b) {
  return (Vec3){.x = a.x - b.x, .y = a.y - b.y, .z = a.z - b.z};
}
static inline Vec3 vec_negate(Vec3 v) {
  return (Vec3){.x = -v.x, .y = -v.y, .z = -v.z};
}
static inline Vec3 vec_multiply(Vec3 a, Vec3 b) {
  return (Vec3){.x = a.x * b.x, .y = a.y * b.y, .z = a.z * b.z};
}

static inline Vec3 vec_normalize2(Vec3 v) {
  // vec_print(v);
  int nor2 = vec_length2(v);
  if (nor2 > 0) {
    int nor = sqrtint(nor2);
    v = vec_divide(vec_scale(v, PRECISION_SQRT), nor);
    // printf("Normalize v %d %d %d, nor2 %d, nor %d\n", v.x, v.y, v.z, nor2,
    // nor);
  }
  return v;
}

static inline Vec3 vec_normalize(Vec3 v) {
  // vec_print(v);
  // Check how much we should scale the values
  if (vec_length2(v) < 0) {
    // Overflow
    int nor2 = vec_length2(vec_divide(v, PRECISION));
    if (nor2 > 0) {
      int nor = sqrtint(nor2 * PRECISION);
      v = vec_divide(v, nor);
    } else {
      printf("OVER1\n");
    }
  } else if (vec_length2(v) > (INT_MAX / PRECISION / 4)) {
    int nor2 = vec_length2(v);
    if (nor2 > 0) {
      int nor = sqrtint(nor2);
      v = vec_divide(vec_scale(v, PRECISION_SQRT), nor);
    } else {
      printf("OVER2\n");
    }
  } else {
    int nor2 = vec_length2(v) * PRECISION;
    if (nor2 > 0) {
      int nor = sqrtint(nor2);
      v = vec_divide(vec_scale(v, PRECISION), nor);
      // printf("Normalize v %d %d %d, nor2 %d, nor %d\n", v.x, v.y, v.z, nor2,
      // nor);
    } else {
      printf("OVER3\n");
    }
  }
  return v;
}

typedef struct Sphere {
  Vec3 center;                      /// position of the sphere
  int radius, radius2;              /// sphere radius and radius^2
  Vec3 surfaceColor, emissionColor; /// surface color and emission (light)
  int transparency, reflection;     /// surface transparency and reflectivity
} Sphere;

Sphere *spheres_ptr[NUM_CORES];

// Compute a ray-sphere intersection using the geometric solution
bool intersect(const Sphere sphere, const Vec3 rayorig, const Vec3 raydir,
               int *t0, int *t1) {
  // vec_print(sphere.center);
  // vec_print(raydir);
  Vec3 l = vec_subtract(sphere.center, rayorig);
  int tca = vec_dot(l, raydir);
  // printf("l %d %d %d, tca %d\n", l.x, l.y, l.z, tca);
  if (tca < 0)
    return false;
  int d2 = vec_length2(l) - tca * tca / PRECISION;
  if (vec_length2(l) < 0) {
    d2 = vec_dot_unscaled(vec_divide(l, PRECISION), vec_divide(l, PRECISION)) -
         (tca / PRECISION) * (tca / PRECISION);
    d2 *= PRECISION;
  }
  // printf("d2 %d\n", d2);
  if (d2 > sphere.radius2)
    return false;
  int thc2 = sphere.radius2 - d2;
  int thc;
  if (thc2 < 0) {
    thc2 = sphere.radius2 / PRECISION - d2 / PRECISION;
    if (thc2 < 0) {
      printf("WTF %d %d %d\n", tca, d2, sphere.radius2);
    }
    thc = sqrtint(thc2) * PRECISION;
  } else if ((thc2 > INT_MAX / PRECISION / 4) ||
             (thc2 < INT_MIN / PRECISION / 4)) {
    thc = sqrtint(thc2) * PRECISION_SQRT;
  } else if ((thc2 > INT_MAX / PRECISION / PRECISION / 4) ||
             (thc2 < INT_MIN / PRECISION / PRECISION / 4)) {
    thc = sqrtint(thc2 * PRECISION);
  } else if ((thc2 > INT_MAX / PRECISION / PRECISION / PRECISION / 4) ||
             (thc2 < INT_MIN / PRECISION / PRECISION / PRECISION / 4)) {
    thc = sqrtint(thc2 * PRECISION * PRECISION) / PRECISION_SQRT;
  } else {
    thc = sqrtint(thc2 * PRECISION * PRECISION * PRECISION) / PRECISION;
  }
  *t0 = tca - thc;
  *t1 = tca + thc;
  // printf("thc %d, t0 %d, t1 %d\n", thc, *t0, *t1);
  return true;
}

//[comment]
// This variable controls the maximum recursion depth
//[/comment]
#define MAX_RAY_DEPTH 5

int mix(const int a, const int b, const int mix) {
  return b * mix + a * (1 - mix);
}

//[comment]
// This is the main trace function. It takes a ray as argument (defined by its
// origin
// and direction). We test if this ray intersects any of the geometry in the
// scene.
// If the ray intersects an object, we compute the intersection point, the
// normal
// at the intersection point, and shade this point using this information.
// Shading depends on the surface property (is it transparent, reflective,
// diffuse).
// The function returns a color for the ray. If the ray intersects an object
// that
// is the color of the object at the intersection point, otherwise it returns
// the background color.
//[/comment]
Vec3 trace(const Vec3 rayorig, const Vec3 raydir, const Sphere *spheres,
           const unsigned num_spheres, const int depth) {
  // if (raydir.length() != 1) std::cerr << "Error " << raydir << std::endl;
  int tnear = INT_MAX;
  int sphere_idx = -1;
  const Sphere *sphere = NULL;
  // find intersection of this ray with the sphere in the scene
  for (unsigned i = 0; i < num_spheres; ++i) {
    int t0 = INT_MAX, t1 = INT_MAX;
    // printf("Check for sphere %d\n", i);
    if (intersect(spheres[i], rayorig, raydir, &t0, &t1)) {
      if (t0 < 0)
        t0 = t1;
      if (t0 < tnear) {
        tnear = t0;
        sphere = &spheres[i];
        sphere_idx = i;
      }
    }
  }
  // printf("Hit sphere %d\n\n", sphere_idx);
  // if there's no intersection return black or background color
  if (!sphere)
    return VEC3_x(200);
  // color of the ray/surfaceof the object intersected by the ray
  Vec3 surfaceColor = VEC3;
  // point of intersection
  Vec3 phit = vec_add(rayorig, vec_divide(vec_scale(raydir, tnear), PRECISION));
  // normal at the intersection point
  Vec3 nhit = vec_subtract(phit, sphere->center);
  // normalize normal direction
  nhit = vec_normalize(nhit);
  // If the normal and the view direction are not opposite to each other
  // reverse the normal direction. That also means we are inside the sphere so
  // set
  // the inside bool to true. Finally reverse the sign of IdotN which we want
  // positive.
  int bias =
      PRECISION / 2; // add some bias to the point from which we will be tracing
  bool inside = false;
  if (vec_dot(raydir, nhit) > 0) {
    nhit = vec_negate(nhit);
    inside = true;
  }
  if ((sphere->transparency > 0 || sphere->reflection > 0) &&
      depth < MAX_RAY_DEPTH) {
    int facingratio = -vec_dot(raydir, nhit) / PRECISION;
    // change the mix value to tweak the effect
    int fresneleffect = 1;
    // int fresneleffect = mix(powint(PRECISION - facingratio, 3),
    //                         0.8 * (PRECISION * PRECISION * PRECISION), 0.2) /
    //                     (PRECISION * PRECISION);
    // compute reflection direction (not need to normalize because all vectors
    // are already normalized)
    Vec3 refldir =
        vec_subtract(raydir, vec_scale(nhit, 2 * vec_dot(raydir, nhit) /
                                                 PRECISION / PRECISION));
    refldir = vec_normalize(refldir);
    Vec3 reflection = trace(vec_add(phit, vec_divide(nhit, bias)), refldir,
                            spheres, num_spheres, depth + 1);
    Vec3 refraction = VEC3;
    // if the sphere is also transparent compute refraction ray (transmission)
    // if (sphere->transparency) {
    //   int ior = 1.1;
    //   int eta =
    //       (inside) ? ior : 1 / ior; // are we inside or outside the surface?
    //   int cosi = -vec_dot(nhit, raydir) / PRECISION;
    //   int k = (PRECISION * PRECISION) -
    //           eta * eta * ((PRECISION * PRECISION) - cosi * cosi);
    //   Vec3 refrdir =
    //       vec_add(vec_scale(raydir, eta),
    //               vec_scale(nhit, (eta * cosi - sqrtint(k)) / PRECISION));
    //   refrdir = vec_normalize(refrdir);
    //   refraction = trace(vec_subtract(phit, vec_divide(nhit, bias)), refrdir,
    //                      spheres, num_spheres, depth + 1);
    // }
    // the result is a mix of reflection and refraction (if the sphere is
    // transparent)
    surfaceColor = vec_multiply(
        vec_add(vec_scale(reflection, fresneleffect * sphere->reflection),
                vec_scale(refraction,
                          (PRECISION - fresneleffect) * sphere->transparency)),
        sphere->surfaceColor);
    surfaceColor = vec_divide(surfaceColor, 256 * PRECISION); // Divide by 256
  } else {
    // it's a diffuse object, no need to raytrace any further
    for (unsigned i = 0; i < num_spheres; ++i) {
      if (spheres[i].emissionColor.x > 0) {
        // this is a light
        int transmission = 1;
        Vec3 lightDirection = vec_subtract(spheres[i].center, phit);
        lightDirection = vec_normalize(lightDirection);
        for (unsigned j = 0; j < num_spheres; ++j) {
          if (i != j) {
            int t0, t1;
            if (intersect(spheres[j], vec_add(phit, vec_divide(nhit, bias)),
                          lightDirection, &t0, &t1)) {
              transmission = 0;
              break;
            }
          }
        }
        int dot = vec_dot(nhit, lightDirection);
        if (dot > 0) {
          transmission *= dot;
          Vec3 tmp = vec_scale(sphere->surfaceColor, transmission);
          tmp = vec_multiply(tmp, spheres[i].emissionColor);
          tmp = vec_divide(tmp, 1); // Divide by 256
          surfaceColor = vec_add(tmp, surfaceColor);
          // surfaceColor = sphere->surfaceColor;
        } else {
          // surfaceColor = VEC3_x(128);
        }
        // surfaceColor = VEC3_x(dot*256/PRECISION);
      }
    }
    // surfaceColor = VEC3_x(32*sphere_idx);
  }

  return vec_divide(vec_add(surfaceColor, sphere->emissionColor),
                    PRECISION * 256);
}

//[comment]
// Main rendering function. We compute a camera ray for each pixel of the image
// trace it and return a color. If the ray hits a sphere, we return the color of
// the
// sphere at the intersection point, else we return the background color.
//[/comment]
void render(const Sphere *spheres, unsigned num_spheres) {
  Vec3 *pixel = image;
// Trace rays
// #pragma omp parallel for firstprivate(pixel) schedule(static)
#pragma omp parallel for collapse(2) firstprivate(pixel) schedule(dynamic, 8)
  for (int x = 0; x < WIDTH; ++x) {
    for (int y = 0; y < HEIGHT; ++y) {
      Vec3 raydir = VEC3_xyz(-WIDTH / 2 + x, HEIGHT / 2 - y, -WIDTH * 1);
      raydir = vec_scale(raydir, 1280 / WIDTH);
      raydir = vec_normalize(raydir);
      // printf("Check pixel %04d, raydir %d %d %d\n", x + y * WIDTH, raydir.x,
      //       raydir.y, raydir.z);
      const Sphere *local_spheres = spheres_ptr[mempool_get_core_id()];
      pixel[x + y * WIDTH] =
          trace(VEC3_x(0), raydir, local_spheres, num_spheres, 0);
    }
  }
  // Save result to a PPM image (keep these flags if you compile under Windows)
  // FILE *fptr;
  // fptr = fopen("./untitled.ppm", "wb");
  // fprintf(fptr, "P6\n%d %d\n255\n", WIDTH, HEIGHT);
  // for (unsigned i = 0; i < WIDTH * HEIGHT; ++i) {
  //   unsigned char x = image[i].x > 255 ? 255 : (unsigned char)(image[i].x);
  //   unsigned char y = image[i].y > 255 ? 255 : (unsigned char)(image[i].y);
  //   unsigned char z = image[i].z > 255 ? 255 : (unsigned char)(image[i].z);
  //   fprintf(fptr, "%c%c%c", x, y, z);
  // }
  // fclose(fptr);
}

//[comment]
// In the main function, we will create the scene which is composed of 5 spheres
// and 1 light (which is also a sphere). Then, once the scene description is
// complete
// we render that scene, by calling the render() function.
//[/comment]
int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  const unsigned num_spheres = 7;
  Sphere spheres[num_spheres];
  // position, radius, surface color, reflectivity, transparency, emission color
  spheres[0] = (Sphere){.center = VEC3_xyz(0, -1004, 0),
                        .radius = 1000,
                        .radius2 = 1000 * 1000,
                        .surfaceColor = VEC3_xyz(80, 80, 80),
                        .emissionColor = VEC3,
                        .transparency = 0,
                        .reflection = 0};
  spheres[1] = (Sphere){.center = VEC3_xyz(0, 0, -20),
                        .radius = 4,
                        .radius2 = 4 * 4,
                        .surfaceColor = VEC3_xyz(87, 117, 144),
                        .emissionColor = VEC3,
                        .transparency = 0,
                        .reflection = 0};
  spheres[2] = (Sphere){.center = VEC3_xyz(5, -1, -15),
                        .radius = 2,
                        .radius2 = 2 * 2,
                        .surfaceColor = VEC3_xyz(249, 199, 79),
                        .emissionColor = VEC3,
                        .transparency = 0,
                        .reflection = 0};
  spheres[3] = (Sphere){.center = VEC3_xyz(5, 0, -25),
                        .radius = 3,
                        .radius2 = 3 * 3,
                        .surfaceColor = VEC3_xyz(144, 190, 109),
                        .emissionColor = VEC3,
                        .transparency = 0,
                        .reflection = 0};
  spheres[4] = (Sphere){.center = VEC3_xyz(-5, 0, -15),
                        .radius = 3,
                        .radius2 = 3 * 3,
                        .surfaceColor = VEC3_xyz(255, 255, 255),
                        .emissionColor = VEC3,
                        .transparency = 0,
                        .reflection = 0};
  // light
  spheres[5] = (Sphere){.center = VEC3_xyz(30, 40, -5),
                        .radius = 1,
                        .radius2 = 1 * 1,
                        .surfaceColor = VEC3_xyz(0, 0, 0),
                        .emissionColor = VEC3_x(255),
                        .transparency = 0,
                        .reflection = 0};
  spheres[6] = (Sphere){.center = VEC3_xyz(-20, 60, 50),
                        .radius = 1,
                        .radius2 = 1 * 1,
                        .surfaceColor = VEC3_xyz(0, 0, 0),
                        .emissionColor = VEC3_x(255),
                        .transparency = 0,
                        .reflection = 0};
  for (unsigned i = 0; i < num_spheres; ++i) {
    spheres[i].center = vec_scale(spheres[i].center, PRECISION);
    spheres[i].radius = spheres[i].radius * PRECISION;
    spheres[i].radius2 = spheres[i].radius2 * PRECISION;
  }

  spheres_ptr[core_id] = spheres;

  if (core_id == 0) {
    mempool_start_benchmark();
    render(spheres, num_spheres);
    mempool_stop_benchmark();
  } else {
    while (1) {
      mempool_wfi();
      mempool_start_benchmark();
      run_task(core_id);
      mempool_stop_benchmark();
    }
  }

  return 0;
}
