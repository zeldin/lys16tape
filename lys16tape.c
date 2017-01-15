#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include <unistd.h>
#include <limits.h>
#include <sys/types.h>
#include <sys/stat.h>

enum {
  VALUE_0,
  VALUE_1,
  VALUE_NONE
};

enum {
  WAIT_HEADER,
  READ_HEADER,
  READ_DATA,
};

static FILE *out_data = NULL;
static FILE *out_file = NULL;
static FILE *out_gnuplot = NULL;
static unsigned gnuplot_min = 0, gnuplot_max = UINT_MAX;
static unsigned data_number = 0;
static const char *data_fn = NULL;
static const char *file_dir = NULL;
static unsigned num_blocks = 0, num_csum_errors = 0;

static int analyze_block(const unsigned char *header, const unsigned char *data)
{
  static const char *types[] = { "TITLE", "???", "DATA", "END" };
  int transient = 0;
  unsigned len = (header[0]<<8)|header[1];
  unsigned type = len>>14;
  len &= 0x3fff;
  printf("BLOCK type %u (%s) len %u", type, types[type], len);
  if (type == 0) {
    num_blocks = 0;
    num_csum_errors = 0;
  }
  if (type == 0 && file_dir != NULL) {
    char *fn, *p;
    if (out_file != NULL) {
      fclose(out_file);
      out_file = NULL;
    }
    if (asprintf(&fn, "%s%s%.*s", file_dir,
		 (file_dir[strlen(file_dir)-1]=='/'? "" : "/"),
		 len*2-4, data+4) < 0) {
      fprintf(stderr, "Out of memory\n");
      return 1;
    }
    p = &fn[strlen(file_dir)-1];
    if (*p!='/') p++;
    p++;
    while ((p=strchr(p, '/')))
      *p++ = '_';
    out_file = fopen(fn, "w");
    if (out_file)
      printf(" - Write to file %s", fn);
    else {
      printf("\n");
      perror(fn);
    }
    free(fn);
    if (!out_file)
      return 1;
  }
  if (type == 2) {
    unsigned i, hdrcsum, csum = 0;
    hdrcsum = (header[2]<<8)|header[3];
    for (i=0; i<len; i++) {
      unsigned v = (data[2*i]<<8)|data[2*i+1];
      csum += v;
      csum &= 0xffff;
    }
    printf(" #%u", num_blocks++);
    if (csum == hdrcsum) {
      printf(" csum ok");
      transient = 1;
    } else {
      printf(" csum mismatch %04x != %04x (%04x)", csum, hdrcsum, (hdrcsum-csum)&0xffff);
      num_csum_errors++;
    }
    if (out_file != NULL)
      fwrite(data+8, 2, len-4, out_file);
  }
  if (type == 3) {
    printf(" - %u blocks", num_blocks);
    if (num_csum_errors)
      printf(", %u with errors", num_csum_errors);
    else
      printf(" all ok");
    num_blocks = 0;
    num_csum_errors = 0;
  }
  if (type == 3 && out_file != NULL) {
    fclose(out_file);
    out_file = NULL;
  }
  if (transient) {
    printf("\r");
    fflush(stdout);
  } else
    printf("\n");
  return 0;
}

static int got_bits(unsigned n, unsigned data, unsigned bitcnt)
{
  static unsigned mode = WAIT_HEADER, pos = 0;
  static unsigned char databuf[0x8000], header[4];

  /* 8N2 */
  if (data&1)
    /* No start bit */
    return 0;
  if (bitcnt < 11 || ((data>>9)&3) != 3)
    /* Missing stop bits */
    return 0;
  data = (data>>1)&0xff;

  if (out_data == NULL && data_fn != NULL) {
    char *fn;
    if (asprintf(&fn, data_fn, ++data_number) < 0) {
      fprintf(stderr, "Out of memory\n");
      return 1;
    }
    if (!(out_data = fopen(fn, "w")))
      perror(fn);
    free(fn);
    if (!out_data)
      return 1;
  }

  if (out_data != NULL)
    fputc(data, out_data);

  if (mode == WAIT_HEADER) {
    if (data == 0x02) {
      mode = READ_HEADER;
    }
  } else if (mode == READ_HEADER) {
    header[pos++] = data;
    if (pos == 4) {
      unsigned len = (((header[0]<<8)|header[1])&0x3fff)*2;
      pos = 0;
      mode = READ_DATA;
      if (!len) {
	printf("*** EMPTY block!?\n");
	mode = WAIT_HEADER;
      }
    }
  } else {
    unsigned len = (((header[0]<<8)|header[1])&0x3fff)*2;
    databuf[pos++] = data;
    if (pos == len)
      mode = WAIT_HEADER;
  }
  if (mode == WAIT_HEADER && pos > 0) {
    pos = 0;
    return analyze_block(header, databuf);
  }

  return 0;
}

static int emit(unsigned n, unsigned v, double l)
{
  static unsigned bitcnt = 0;
  static unsigned data = 0;
  int r = 0;
  if(v == VALUE_NONE) {
    if (bitcnt)
      r = got_bits(n, data, bitcnt);
    bitcnt = 0;
    data = 0;
    return r;
  }
  unsigned cnt = round(l);
  if (v == VALUE_0 && bitcnt >= 10) {
    r = got_bits(n, data, bitcnt);
    bitcnt = 0;
    data = 0;
  }
  if (v == VALUE_1 && bitcnt < 30) {
    unsigned xcnt = (cnt > 30? 30 : cnt);
    data |= ((1U<<xcnt)-1) << bitcnt;
  }
  bitcnt += cnt;
  return r;
}

static void butterworth3(unsigned fs, unsigned f0, double *a, double *b)
{
  double omega = 8*atan(1.0)*f0/fs;
  double common = omega*omega + 2*omega + 4;
  /* Real pole */
  double k1 = (2-omega)/(2+omega);
  /* Complex poles */
  double k2 = (4-omega*omega) / common;
  double k3 = 2*sqrt(3)*omega / common;

  a[0] = 1;
  a[1] = -(k1+2*k2);
  a[2] = k2*k2+k3*k3+2*k1*k2;
  a[3] = -k1*(k2*k2+k3*k3);

  b[0] = (1+a[1]+a[2]+a[3])/8;
  b[1] = b[0]*3;
  b[2] = b[1];
  b[3] = b[0];
}

static int process(FILE *f, unsigned fs, unsigned br, unsigned k)
{
  unsigned i, n = 0;
  static float buf[65536];
  static double s[256], x[256], y[256], pwr[256];
  double a[4], b[4];
  size_t cnt;
  unsigned last_pos = 0, v = VALUE_NONE, last_value = VALUE_NONE;
  double o, gain, sumpwr = 0;
  double samplesperbit = ((double)fs)/br;
  unsigned agcdelay = round(samplesperbit);

  if (k >= 256 || agcdelay >= 256) {
    fprintf(stderr, "Wraparound error!\n");
    return 1;
  }

  butterworth3(fs, br, a, b);

  for(i=0; i<256; i++) {
    s[i] = 0;
    x[i] = 0;
    y[i] = 0;
    pwr[i] = 0;
  }
  while((cnt = fread(buf, sizeof(buf[0]), sizeof(buf)/sizeof(buf[0]), f)))
    for(i=0; i<cnt; i++) {
      pwr[n&255] = buf[i]*buf[i];
      sumpwr = sumpwr + pwr[n&255] - pwr[(n-agcdelay)&255];
      gain = agcdelay / sumpwr;

      s[n&255] = buf[i];

      /* Delayed product, input to LP filter */
      x[n&255] = s[n&255]*s[(n-k)&255];

      /* IIR filter */
      y[n&255] = o =
	b[0]*x[n&255] + b[1]*x[(n-1)&255] +
	b[2]*x[(n-2)&255] + b[3]*x[(n-3)&255]
	- a[1]*y[(n-1)&255] - a[2]*y[(n-2)&255]
	- a[3]*y[(n-3)&255];

      o *= gain;

      if (gain > 1000000.0 ||
	  (last_value == VALUE_NONE && gain > 1000.0))
	v = VALUE_NONE;
      else if (o < 0.4)
	v = VALUE_0;
      else if (o > 0.5)
	v = VALUE_1;

      if (v != last_value) {
	if (last_pos != n)
	  if (emit(last_pos, last_value, (n-last_pos)/samplesperbit))
	    return 1;
	if (last_value == VALUE_NONE)
	  printf("Signal detected at %u\n", n);
	else if (v == VALUE_NONE) {
	  printf("Signal lost at %u\n", n);
	  if (out_file != NULL) {
	    fclose(out_file);
	    out_file = NULL;
	  }
	  if (out_data != NULL) {
	    fclose(out_data);
	    out_data = NULL;
	  }
	}
	last_pos = n;
	last_value = v;
      }

      if (out_gnuplot && n >= gnuplot_min && n < gnuplot_max)
	fprintf(out_gnuplot, "%u %f %f %f %f\n",
		n, s[(n&255)], y[(n&255)], o, gain);

      n++;
    }
  if (ferror(f)) {
    perror("fread");
    return 1;
  }
  return 0;
}

static FILE *vapopen(const char *mode, const char *fmt, ...)
{
  char *cmd;
  va_list va;
  va_start(va, fmt);
  if (vasprintf(&cmd, fmt, va) < 0) {
    fprintf(stderr, "Out of memory\n");
    return NULL;
  }
  FILE *f = popen(cmd, mode);
  free(cmd);
  if (!f)
    perror(NULL);
  return f;
}

unsigned getrate(const char *fn)
{
  unsigned rate;
  FILE *f = vapopen("r", "soxi -r '%s'", fn);
  if (!f)
    return 0;
  if (fscanf(f, "%u", &rate) != 1) {
    fprintf(stderr, "Unable to detect samplerate\n");
    rate = 0;
  }
  pclose(f);
  return rate;
}

static int check_format(const char *fmt, const char *allowed)
{
  const char *c = strchr(fmt, '%');
  while (c && c[1] == '%')
    c = strchr(c+2, '%');
  if (strchr(c+1, '%')) {
    fprintf(stderr, "Error: Multiple %% conversions found in filename\n");
    return 1;
  }
  while(*++c)
    if (strchr(allowed, *c))
      return 0;
    else switch(*c) {
    case '#': case '0': case '1': case '2': case '3': case '4': case '5':
    case '6': case '7': case '8': case '9': case '-': case ' ': case '+':
    case '\'': case 'I': case '.':
      /* Allowed modifier */
      break;
    default:
      fprintf(stderr, "Error: Unallowed %% conversion found in filename\n");
      return 1;
    }
  fprintf(stderr, "Error: Unterminated %% conversion found in filename\n");
  return 1;
}

static int check_dir(const char *fn)
{
  struct stat s;
  if (!*fn) {
    fprintf(stderr, "Empty directory name specified!\n");
    return 1;
  }
  if (stat(fn, &s)<0) {
    perror(fn);
    return 1;
  }
  if (!S_ISDIR(s.st_mode)) {
    fprintf(stderr, "%s: Not a directory\n", fn);
    return 1;
  }
  return 0;
}

static const char usage[] =
  "Usage: %s [options] input_audio_file\n"
  "  -l          Use left channel of audiofile\n"
  "  -r          Use right channel of audiofile\n"
  "  -m          Use L+R mix of audiofile\n"
  "  -k number   Specify k for FSK decoder\n"
  "  -b baud     Specify baudrate for data signal\n"
  "  -G file     Write gzipped gnuplot data to file\n"
  "  -s pos      Start position for gnuplot data\n"
  "  -e pos      End position for gnuplot data\n"
  "  -D file     Write raw data to file, use %%u for index number\n"
  "  -F dir      Extract files into dir, load address will be discarded\n"
;

int main(int argc, char *argv[])
{
  const char *fn, *gnuplot_fn = NULL;
  int r, opt;
  FILE *f;
  unsigned rate;
  const char *mix = "1";
  unsigned baud = 600, k = 0;

  while ((opt = getopt(argc, argv, "lrmk:b:G:s:e:D:F:")) != -1)
    switch (opt) {
    case 'l': mix = "1"; break;
    case 'r': mix = "2"; break;
    case 'm': mix = "1-2"; break;
    case 'k':
      k = atoi(optarg);
      break;
    case 'b':
      baud = atoi(optarg);
      break;
    case 'G':
      gnuplot_fn = optarg;
      break;
    case 's':
      gnuplot_min = atoi(optarg);
      break;
    case 'e':
      gnuplot_max = atoi(optarg);
      break;
    case 'D':
      if (check_format(optarg, "uxXo"))
	return 1;
      data_fn = optarg;
      break;
    case 'F':
      if (check_dir(optarg))
	return 1;
      file_dir = optarg;
      break;
    default:
      fprintf(stderr, usage, argv[0]);
      return 1;
    }

  if (argc != optind+1) {
    fprintf(stderr, usage, argv[0]);
    return 1;
  }

  fn = argv[optind];

  if (strchr(fn, '\'') || strchr(fn, '\\')) {
    fprintf(stderr, "Input filename must not contain ' or \\.\n");
    return 1;
  }

  if (gnuplot_fn && (strchr(gnuplot_fn, '\'') || strchr(gnuplot_fn, '\\'))) {
    fprintf(stderr, "Output filename must not contain ' or \\.\n");
    return 1;
  }

  if (!(rate  = getrate(fn)))
    return 1;

  if (k == 0)
    switch(rate) {
    case 44100: k=10; break;
    case 48000: k=11; break;
    default:
      fprintf(stderr, "Don't know what k to use for samplerate %u, please use -k\n", rate);
      return 1;
    }

  if (!(f = vapopen("r", "sox '%s' -t raw -e floating-point -b 32 - remix %s",
		    fn, mix)))
    return 1;

  if (gnuplot_fn != NULL &&
      !(out_gnuplot = vapopen("w", "gzip -c > '%s'", gnuplot_fn)))
    r = 1;
  else
    r = process(f, rate, baud, k);
  pclose(f);
  if (out_data != NULL)
    fclose(out_data);
  if (out_file != NULL)
    fclose(out_file);
  if (out_gnuplot != NULL)
    pclose(out_gnuplot);
  return r;
}
