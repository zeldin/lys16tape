#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include <unistd.h>

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

static void analyze_block(const unsigned char *header, const unsigned char *data)
{
  static const char *types[] = { "TITLE", "???", "DATA", "END" };
  unsigned len = (header[0]<<8)|header[1];
  unsigned type = len>>14;
  len &= 0x3fff;
  printf("BLOCK type %u (%s) len %u", type, types[type], len);
  if (type == 2) {
    unsigned i, hdrcsum, csum = 0;
    hdrcsum = (header[2]<<8)|header[3];
    for (i=0; i<len; i++) {
      unsigned v = (data[2*i]<<8)|data[2*i+1];
      csum += v;
      csum &= 0xffff;
    }
    if (csum == hdrcsum)
      printf(" csum ok");
    else
      printf(" csum mismatch %04x != %04x (%04x)", csum, hdrcsum, (hdrcsum-csum)&0xffff);
    if (out_file != NULL)
      fwrite(data+8, 2, len-4, out_file);
  }
  if (type == 3 && out_file != NULL) {
    fclose(out_file);
    out_file = NULL;
  }
  printf("\n");
}

static void got_bits(unsigned data, unsigned bitcnt)
{
  static unsigned mode = WAIT_HEADER, pos = 0;
  static unsigned char databuf[0x8000], header[4];

  /* 8N2 */
  if (data&1)
    /* No start bit */
    return;
  if (bitcnt < 11 || ((data>>9)&3) != 3)
    /* Missing stop bits */
    return;
  data = (data>>1)&0xff;

  if (out_data != NULL)
    fputc(data, out_data);

  if (mode == WAIT_HEADER) {
    if (data == 0x02)
      mode = READ_HEADER;
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
    analyze_block(header, databuf);
    pos = 0;
  }
}

static void emit(unsigned n, unsigned v, double l)
{
  static unsigned bitcnt = 0;
  static unsigned data = 0;
  if(v == VALUE_NONE) {
    if (bitcnt)
      got_bits(data, bitcnt);
    bitcnt = 0;
    data = 0;
    return;
  }
  unsigned cnt = round(l);
  if (v == VALUE_0 && bitcnt >= 10) {
    got_bits(data, bitcnt);
    bitcnt = 0;
    data = 0;
  }
  if (v == VALUE_1 && bitcnt < 30) {
    unsigned xcnt = (cnt > 30? 30 : cnt);
    data |= ((1U<<xcnt)-1) << bitcnt;
  }
  bitcnt += cnt;
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

      if (gain > 1000000.0)
	v = VALUE_NONE;
      else if (o < 0.4)
	v = VALUE_0;
      else if (o > 0.5)
	v = VALUE_1;

      if (v != last_value) {
	if (last_pos != n)
	  emit(last_pos, last_value, (n-last_pos)/samplesperbit);
	last_pos = n;
	last_value = v;
      }

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

static const char usage[] =
  "Usage: %s [options] input_audio_file\n"
  "  -l          Use left channel of audiofile\n"
  "  -r          Use right channel of audiofile\n"
  "  -m          Use L+R mix of audiofile\n"
  "  -k number   Specify k for FSK decoder\n"
  "  -b baud     Specify baudrate for data signal\n"
  ;

int main(int argc, char *argv[])
{
  const char *fn;
  int r, opt;
  FILE *f;
  unsigned rate;
  const char *mix = "1";
  unsigned baud = 600, k = 10;

  while ((opt = getopt(argc, argv, "lrmk:b:")) != -1)
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

  if (!(rate  = getrate(fn)))
    return 1;
  if (!(f = vapopen("r", "sox '%s' -t raw -e floating-point -b 32 - remix %s",
		    fn, mix)))
    return 1;
  r = process(f, rate, baud, k);
  pclose(f);
  if (out_data != NULL)
    fclose(out_data);
  if (out_file != NULL)
    fclose(out_file);
  return r;
}
